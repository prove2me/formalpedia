-- Prove2me | Theorems.Thm_StreamSubmod_Supplement_proposition_29
-- name    : StreamSubmod.Supplement.proposition_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:49:04.092267+00:00
-- url     : https://prove2.me/theorems/e0303bc7-0973-5c1b-9286-8c9e91bc42e6
-- title:
--   Proposition 29: Algorithm 3 stores $O(k/p)$ elements and, with $c=\alpha(1-p)/(\alpha+1)$, has expected value $\ge\alpha\tau(1-p)/(\alpha+1)$
-- statement:
--   There is a universal constant $C>0$ such that the following holds for every finite ground set $V$, every non-negative submodular $f:2^V\to\mathbb R_{\ge0}$, every $k\ge1$ and every $p\in(0,1)$.
--
--   1. **Space.** For every $c>0$, every $0\le\tau\le f(\mathrm{OPT})$ and every stream presenting each element of $V$ exactly once, after every prefix of the stream the fractional solution $x$ of Algorithm 3 has $|\operatorname{supp}(x)|\le C\cdot k/p$; Algorithm 3 stores only these elements.
--   2. **Value.** For every $\alpha$-approximation offline algorithm OfflineAlg ($0<\alpha\le1$), every rounding procedure for line 4, every $0\le\tau\le f(\mathrm{OPT})$ and every such stream, Algorithm 3 with $c=\alpha(1-p)/(\alpha+1)$ returns a set of expected value
--
--   $$
--   \mathbb E[f(\text{output})]\ \ge\ \frac{\alpha\tau(1-p)}{\alpha+1}.
--   $$
--
--   This summarizes the analysis of Algorithm 3 for a known estimate $\tau$.
--
--   Differences from the source:
--   - encoding: O(·) → one universal constant C, chosen before the ground set, f, k and every parameter of the algorithm; reason: this is the meaning of O(·) with all parameters shown
--   - encoding: the number of elements Algorithm 3 stores → |supp(x)| for the fractional solution x after every prefix of the stream, the empty prefix included; reason: by the proof of Observation 21 (p.23), Algorithm 3 needs to store only the elements of supp(x)
--   - encoding: a "semi-streaming algorithm" → the left fold alg3Run over the stream with the stated bound on stored elements after every prefix; reason: the bound on the stored elements is what semi-streaming asks of the memory
--   - generalization: Appendix C assumes an estimate τ with (1 − ε/8)·f(OPT) ≤ τ ≤ f(OPT) (p.21) → 0 ≤ τ ≤ f(OPT); reason: the result does not involve ε, and since f ≥ 0 the section's window implies 0 ≤ τ ≤ f(OPT), so the Lean statement covers every τ the paper allows
--   - encoding: the elements of V arrive one at a time, in an arbitrary order → a duplicate-free list σ containing every element of E (IsStream), for every such list; reason: this is a single pass over V; no arrival order is excluded
--   - encoding: k is a cardinality bound, never stated to be positive → the hypothesis 1 ≤ k; reason: this excludes only k = 0, where the threshold cτ/k of Algorithm 3 is undefined
--   - reading: line 4: round x to a feasible S₁ with E[f(S₁)] ≥ F(x) (Pipage or Swap Rounding, p.22) → any procedure R with finite seeds ω' of law ν satisfying IsRounding: for every x ∈ [0,1]^E with ‖x‖₁ ≤ k each R ω' x has at most k elements and lies in supp(x), and Σ ν(ω') f(R ω' x) ≥ F(x); reason: the statement holds for every rounding with the guarantees the paper names; the outputs lie in supp(x) because, by the proof of Observation 21 (p.23), Algorithm 3 needs access only to the elements of supp(x) to calculate S₁ and S₂, as is the case for Pipage and Swap Rounding
--   - encoding: E[max{f(S₁), f(S₂)}], the expected value of the output → Σ_ω Σ_ω' μ(ω) ν(ω') f(better f S₁ S₂), with S₁ = R ω' x̂ and S₂ = Off ω (supp x̂); reason: the rounding and OfflineAlg use independent randomness, and better f S₁ S₂ is a set of value max{f(S₁), f(S₂)}
--   - encoding: a possibly randomized OfflineAlg → a finite seed type Ω with a probability vector μ; Off ω U is the output on U with seed ω; reason: outputs are subsets of a finite set, so every randomized algorithm has this form
--   - generalization: OfflineAlg is an α-approximation algorithm for every instance of the problem → IsApproxOffline f k α μ Off: the guarantee is assumed only for the given f and k, on every ground set U ⊆ V; reason: Algorithm 3 calls OfflineAlg only with this f and k, so an algorithm that is α-approximate on every instance satisfies the hypothesis
-- source:
--   Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3, Proposition 29, p.27

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
/-- Proposition 29 (Alaluf, Ene, Feldman, Nguyen & Suh, arXiv:1911.12959v3, p.27): Algorithm 3 is a
semi-streaming algorithm storing `O(k/p)` elements. Moreover, for the value of the parameter `c`
given in Corollary 28 (`c = α(1 − p)/(α + 1)`), the output set produced by this algorithm has an
expected value of at least `ατ(1 − p)/(α + 1)`.

**Formalization Note.** The stored elements after a prefix `L` of the stream are those of
`supp(x)` for `x = alg3Run f k p c τ L` (proof of Observation 21, p.23); the empty prefix is
included, and the storage bound holds for every `c > 0`. The constant `C` of `O(·)` is universal:
it is chosen before the ground set, `f`, `k`, `p`, `c`, `α` and `τ`. The output is the better
of `S₁ = R ω' x̂` and `S₂ = Off ω (supp x̂)`, with independent seeds; the expectation is
`Σ_ω Σ_ω' μ(ω) ν(ω') f(output)`. Appendix C assumes `(1 − ε/8) · f(OPT) ≤ τ ≤ f(OPT)` (p.21);
this result does not involve `ε` and is stated under `0 ≤ τ ≤ f(OPT)`. -/
theorem proposition_29 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (E : Type) [Fintype E] [DecidableEq E] (f : Finset E → ℝ), (∀ S, 0 ≤ f S) →
      Submodular f →
      ∀ k : ℕ, 1 ≤ k → ∀ p : ℝ, 0 < p → p < 1 →
      (∀ c : ℝ, 0 < c → ∀ τ : ℝ, 0 ≤ τ → τ ≤ optVal f k →
        ∀ σ : List E, IsStream σ →
        ∀ L, L <+: σ → ((supp (alg3Run f k p c τ L)).card : ℝ) ≤ C * (k : ℝ) / p) ∧
      (∀ α : ℝ, 0 < α → α ≤ 1 →
        ∀ (Ω : Type) [Fintype Ω] (μ : Ω → ℝ) (Off : Ω → Finset E → Finset E),
        IsApproxOffline f k α μ Off →
        ∀ (Ω' : Type) [Fintype Ω'] (ν : Ω' → ℝ) (R : Ω' → (E → ℝ) → Finset E),
        IsRounding f k ν R →
        ∀ τ : ℝ, 0 ≤ τ → τ ≤ optVal f k →
        ∀ σ : List E, IsStream σ →
        let c := α * (1 - p) / (α + 1)
        α * τ * (1 - p) / (α + 1) ≤
          ∑ ω, ∑ ω', μ ω * ν ω' * f (alg3Out f k p c τ Off R σ ω ω')) := by sorry

end StreamSubmod.Supplement
