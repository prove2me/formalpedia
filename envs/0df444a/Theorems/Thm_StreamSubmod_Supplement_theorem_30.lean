-- Prove2me | Theorems.Thm_StreamSubmod_Supplement_theorem_30
-- name    : StreamSubmod.Supplement.theorem_30
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:49:48.161979+00:00
-- url     : https://prove2.me/theorems/02a9b49f-52de-4957-a461-4ce8d399a83b
-- title:
--   Theorem 30: Algorithm 3 with $p=\varepsilon/2$ and an estimate $\tau$ is an $(\alpha/(1+\alpha)-\varepsilon)$-approximation storing $O(k\varepsilon^{-1})$ elements
-- statement:
--   There is a universal constant $C>0$ with the following property. Let $V$ be a finite ground set, $f:2^V\to\mathbb R_{\ge0}$ non-negative and submodular, $k\ge1$, OfflineAlg an $\alpha$-approximation offline algorithm with $0<\alpha\le1$, and the rounding of line 4 any rounding procedure (feasible, inside the support, expected value at least $F(x)$). Let $\varepsilon\in(0,1]$ and let $\tau$ be an estimate of $f(\mathrm{OPT})$ with
--
--   $$
--   \Bigl(1-\frac{\varepsilon}{8}\Bigr)\cdot f(\mathrm{OPT})\ \le\ \tau\ \le\ f(\mathrm{OPT}).
--   $$
--
--   Run Algorithm 3 with $p=\varepsilon/2$ and $c=\alpha(1-p)/(\alpha+1)$ on any stream presenting each element of $V$ exactly once. Then:
--
--   1. the output is a feasible solution (at most $k$ elements) for every outcome of the randomness;
--   2. its expected value is at least $\bigl(\frac{\alpha}{1+\alpha}-\varepsilon\bigr)\cdot f(\mathrm{OPT})$;
--   3. after every prefix of the stream the algorithm stores at most $C\cdot k\varepsilon^{-1}$ elements (the support of its fractional solution).
--
--   This is the multilinear-extension counterpart, for a known estimate of $f(\mathrm{OPT})$, of the paper's main result.
--
--   Differences from the source:
--   - generalization: "there exists" a semi-streaming algorithm → Algorithm 3 with p = ε/2 and c = α(1 − p)/(α + 1), the algorithm of the proof (p.27); reason: a statement about the witness implies the existence claim
--   - generalization: OfflineAlg has space complexity nearly linear in the size of the ground set (Theorem 18's hypothesis, inherited by Appendix C) → no space hypothesis on Off; reason: that hypothesis only makes the post-processing semi-streaming; the value and storage guarantees hold for every Off
--   - encoding: O(·) → one universal constant C, chosen before the ground set, f, k and every parameter of the algorithm; reason: this is the meaning of O(·) with all parameters shown
--   - encoding: the number of elements Algorithm 3 stores → |supp(x)| for the fractional solution x after every prefix of the stream, the empty prefix included; reason: by the proof of Observation 21 (p.23), Algorithm 3 needs to store only the elements of supp(x)
--   - encoding: a "semi-streaming algorithm" → the left fold alg3Run over the stream with the stated bound on stored elements after every prefix; reason: the bound on the stored elements is what semi-streaming asks of the memory
--   - encoding: the elements of V arrive one at a time, in an arbitrary order → a duplicate-free list σ containing every element of E (IsStream), for every such list; reason: this is a single pass over V; no arrival order is excluded
--   - encoding: k is a cardinality bound, never stated to be positive → the hypothesis 1 ≤ k; reason: this excludes only k = 0, where the threshold cτ/k of Algorithm 3 is undefined
--   - reading: line 4: round x to a feasible S₁ with E[f(S₁)] ≥ F(x) (Pipage or Swap Rounding, p.22) → any procedure R with finite seeds ω' of law ν satisfying IsRounding: for every x ∈ [0,1]^E with ‖x‖₁ ≤ k each R ω' x has at most k elements and lies in supp(x), and Σ ν(ω') f(R ω' x) ≥ F(x); reason: the statement holds for every rounding with the guarantees the paper names; the outputs lie in supp(x) because, by the proof of Observation 21 (p.23), Algorithm 3 needs access only to the elements of supp(x) to calculate S₁ and S₂, as is the case for Pipage and Swap Rounding
--   - encoding: E[max{f(S₁), f(S₂)}], the expected value of the output → Σ_ω Σ_ω' μ(ω) ν(ω') f(better f S₁ S₂), with S₁ = R ω' x̂ and S₂ = Off ω (supp x̂); reason: the rounding and OfflineAlg use independent randomness, and better f S₁ S₂ is a set of value max{f(S₁), f(S₂)}
--   - encoding: a possibly randomized OfflineAlg → a finite seed type Ω with a probability vector μ; Off ω U is the output on U with seed ω; reason: outputs are subsets of a finite set, so every randomized algorithm has this form
--   - generalization: OfflineAlg is an α-approximation algorithm for every instance of the problem → IsApproxOffline f k α μ Off: the guarantee is assumed only for the given f and k, on every ground set U ⊆ V; reason: Algorithm 3 calls OfflineAlg only with this f and k, so an algorithm that is α-approximate on every instance satisfies the hypothesis
-- source:
--   Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3, Theorem 30 and its proof, p.27

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_StreamSubmod_optVal
import Definitions.Def_StreamSubmod_IsStream
import Definitions.Def_StreamSubmod_IsApproxOffline
import Definitions.Def_StreamSubmod_Supplement_Basic
import Definitions.Def_StreamSubmod_Supplement_IsRounding
import Definitions.Def_StreamSubmod_Supplement_Algorithm3

namespace StreamSubmod.Supplement

open NonmonotoneSubmod.Shared StreamSubmod in
/-- Theorem 30 (Alaluf, Ene, Feldman, Nguyen & Suh, arXiv:1911.12959v3, p.27): for every constant
`ε ∈ (0, 1]`, there exists a semi-streaming algorithm that assumes access to an estimate `τ` of
`f(OPT)` obeying `(1 − ε/8) · f(OPT) ≤ τ ≤ f(OPT)` and provides `(α/(1+α) − ε)`-approximation for
the problem of maximizing a non-negative submodular function subject to cardinality constraint. This
algorithm stores at most `O(kε⁻¹)` elements. Stated for the algorithm of the proof (p.27):
Algorithm 3 with `p = ε/2` and `c = α(1 − p)/(α + 1)`.

**Formalization Note.** OfflineAlg is an `α`-approximation with seeds `ω` of probability `μ ω`
(`IsApproxOffline`), and line 4's rounding is any procedure `R` with seeds `ω'` of probability
`ν ω'` satisfying `IsRounding`. The output is the better of `S₁ = R ω' x̂` and
`S₂ = Off ω (supp x̂)`, with independent seeds; the expectation is
`Σ_ω Σ_ω' μ(ω) ν(ω') f(output)`. The stored elements after a prefix `L` of the stream are those of
`supp(x)` for `x = alg3Run f k p c τ L` (proof of Observation 21, p.23), the empty prefix
included. The constant `C` of `O(·)` is universal: it is chosen before the ground set, `f`, `k`,
`α`, `ε` and `τ`. -/
theorem theorem_30 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (E : Type) [Fintype E] [DecidableEq E] (f : Finset E → ℝ), (∀ S, 0 ≤ f S) →
      Submodular f →
      ∀ k : ℕ, 1 ≤ k → ∀ α : ℝ, 0 < α → α ≤ 1 →
      ∀ (Ω : Type) [Fintype Ω] (μ : Ω → ℝ) (Off : Ω → Finset E → Finset E),
      IsApproxOffline f k α μ Off →
      ∀ (Ω' : Type) [Fintype Ω'] (ν : Ω' → ℝ) (R : Ω' → (E → ℝ) → Finset E),
      IsRounding f k ν R →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ τ : ℝ, (1 - ε / 8) * optVal f k ≤ τ → τ ≤ optVal f k →
      ∀ σ : List E, IsStream σ →
      let p := ε / 2
      let c := α * (1 - p) / (α + 1)
      (∀ ω ω', (alg3Out f k p c τ Off R σ ω ω').card ≤ k) ∧
      (α / (1 + α) - ε) * optVal f k ≤
        ∑ ω, ∑ ω', μ ω * ν ω' * f (alg3Out f k p c τ Off R σ ω ω') ∧
      (∀ L, L <+: σ → ((supp (alg3Run f k p c τ L)).card : ℝ) ≤ C * (k : ℝ) * ε⁻¹) := by sorry

end StreamSubmod.Supplement
