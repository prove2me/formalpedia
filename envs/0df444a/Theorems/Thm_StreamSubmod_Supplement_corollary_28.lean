-- Prove2me | Theorems.Thm_StreamSubmod_Supplement_corollary_28
-- name    : StreamSubmod.Supplement.corollary_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:48:33.564876+00:00
-- url     : https://prove2.me/theorems/a1806a0b-ad4e-42d3-8d22-429f19599bef
-- title:
--   Corollary 28: with $c=\alpha(1-p)/(\alpha+1)$ and $\|\hat x\|_1<k$, $\mathbb E[\max\{f(S_1),f(S_2)\}]\ge(1-p)\alpha\tau/(\alpha+1)$
-- statement:
--   Let $V$ be a finite ground set, $f:2^V\to\mathbb R_{\ge0}$ non-negative and submodular, $k\ge1$, $p\in(0,1)$ and $0\le\tau\le f(\mathrm{OPT})$. Let OfflineAlg be an $\alpha$-approximation offline algorithm, $0<\alpha\le1$, and let the rounding of line 4 be any rounding procedure (feasible, inside the support, expected value at least $F(x)$). Run Algorithm 3 with parameters $p$ and
--
--   $$
--   c=\frac{\alpha(1-p)}{\alpha+1}
--   $$
--
--   on a stream presenting each element of $V$ exactly once, in an arbitrary order, and let $\hat x$ be its final fractional solution. If $\|\hat x\|_1<k$, then the output, the better of $S_1$ and $S_2$, satisfies
--
--   $$
--   \mathbb E\bigl[\max\{f(S_1),f(S_2)\}\bigr]\ \ge\ \frac{(1-p)\,\alpha\tau}{\alpha+1}.
--   $$
--
--   Together with Lemma 22 this covers both cases of the analysis.
--
--   Differences from the source:
--   - generalization: Appendix C assumes an estimate τ with (1 − ε/8)·f(OPT) ≤ τ ≤ f(OPT) (p.21) → 0 ≤ τ ≤ f(OPT); reason: the result does not involve ε, and since f ≥ 0 the section's window implies 0 ≤ τ ≤ f(OPT), so the Lean statement covers every τ the paper allows
--   - encoding: the elements of V arrive one at a time, in an arbitrary order → a duplicate-free list σ containing every element of E (IsStream), for every such list; reason: this is a single pass over V; no arrival order is excluded
--   - encoding: k is a cardinality bound, never stated to be positive → the hypothesis 1 ≤ k; reason: this excludes only k = 0, where the threshold cτ/k of Algorithm 3 is undefined
--   - reading: line 4: round x to a feasible S₁ with E[f(S₁)] ≥ F(x) (Pipage or Swap Rounding, p.22) → any procedure R with finite seeds ω' of law ν satisfying IsRounding: for every x ∈ [0,1]^E with ‖x‖₁ ≤ k each R ω' x has at most k elements and lies in supp(x), and Σ ν(ω') f(R ω' x) ≥ F(x); reason: the statement holds for every rounding with the guarantees the paper names; the outputs lie in supp(x) because, by the proof of Observation 21 (p.23), Algorithm 3 needs access only to the elements of supp(x) to calculate S₁ and S₂, as is the case for Pipage and Swap Rounding
--   - encoding: E[max{f(S₁), f(S₂)}], the expected value of the output → Σ_ω Σ_ω' μ(ω) ν(ω') f(better f S₁ S₂), with S₁ = R ω' x̂ and S₂ = Off ω (supp x̂); reason: the rounding and OfflineAlg use independent randomness, and better f S₁ S₂ is a set of value max{f(S₁), f(S₂)}
--   - encoding: a possibly randomized OfflineAlg → a finite seed type Ω with a probability vector μ; Off ω U is the output on U with seed ω; reason: outputs are subsets of a finite set, so every randomized algorithm has this form
--   - generalization: OfflineAlg is an α-approximation algorithm for every instance of the problem → IsApproxOffline f k α μ Off: the guarantee is assumed only for the given f and k, on every ground set U ⊆ V; reason: Algorithm 3 calls OfflineAlg only with this f and k, so an algorithm that is α-approximate on every instance satisfies the hypothesis
-- source:
--   Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3, Corollary 28, p.26

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
/-- Corollary 28 (Alaluf, Ene, Feldman, Nguyen & Suh, arXiv:1911.12959v3, p.26): if `‖x̂‖₁ < k` and
`c` is set to `α(1 − p)/(α + 1)`, then `E[max{f(S₁), f(S₂)}] ≥ (1 − p)ατ/(α + 1)`.

**Formalization Note.** `x̂ = alg3Run f k p c τ σ` is the final fractional solution of Algorithm 3
on the stream `σ`. Appendix C assumes `(1 − ε/8) · f(OPT) ≤ τ ≤ f(OPT)` (p.21); this result does
not involve `ε` and is stated under `0 ≤ τ ≤ f(OPT)`, which that assumption implies. The output of Algorithm 3 is the better of `S₁ = R ω' x̂` (rounding with seed `ω'`, law
`ν`) and `S₂ = Off ω (supp x̂)` (OfflineAlg with seed `ω`, law `μ`); the two seeds are
independent, and the expectation is `Σ_ω Σ_ω' μ(ω) ν(ω') f(output)`. -/
theorem corollary_28 {E : Type} [Fintype E] [DecidableEq E] (f : Finset E → ℝ)
    (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f) (k : ℕ) (hk : 1 ≤ k) (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) {Ω : Type} [Fintype Ω] (μ : Ω → ℝ)
    (Off : Ω → Finset E → Finset E) (hOff : IsApproxOffline f k α μ Off)
    {Ω' : Type} [Fintype Ω'] (ν : Ω' → ℝ) (R : Ω' → (E → ℝ) → Finset E)
    (hR : IsRounding f k ν R)
    (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ optVal f k) (σ : List E) (hσ : IsStream σ) :
    let c := α * (1 - p) / (α + 1)
    l1 (alg3Run f k p c τ σ) < (k : ℝ) →
      (1 - p) * α * τ / (α + 1) ≤
        ∑ ω, ∑ ω', μ ω * ν ω' * f (alg3Out f k p c τ Off R σ ω ω') := by sorry

end StreamSubmod.Supplement
