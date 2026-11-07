-- Prove2me | Theorems.Thm_SubmodSparsify_step_4_support
-- name    : SubmodSparsify.step_4_support
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:23:25.324646+00:00
-- url     : https://prove2.me/theorems/e2d4d2b2-98e4-4dc6-8a28-2c561130c175
-- title:
--   §4.3, Step 4 — the support bound $\Pr[|\mathrm{supp}(w)| > 2\Lambda\sum_i p_i] < \delta/2$
-- statement:
--   Let $f_1, \dots, f_m : 2^{[n]} \to \mathbb R_{\ge 0}$ be submodular with $f_i(\emptyset) = f_i([n]) = 0$, with Algorithm 1's weights $p_i$, and let $\varepsilon, \delta \in (0,1)$, $\Lambda := 56\varepsilon^{-2}\log(32n/\delta)$, and $N := |\mathrm{supp}(w)|$ the number of sampled components under independent $\min\{1, \Lambda p_i\}$-sampling. Then
--
--   $$\Pr\Bigl[N > 2\Lambda \sum_{i=1}^m p_i\Bigr] \le \exp\Bigl(-(2\log 2 - 1)\Lambda \sum_{i=1}^m p_i\Bigr) \qquad \text{and} \qquad \Pr\Bigl[N > 2\Lambda \sum_{i=1}^m p_i\Bigr] < \frac{\delta}{2}.$$
--
--   Together with $\sum_i p_i \le 2n(n-1)$ this gives the sparsity $N \le 4\Lambda n(n-1)$ of Theorem 4.1.
--
--   Differences from the source:
--   - encoding: ground set [n] = {1, …, n}, subsets of [n], components f_1, …, f_m → Fin n (paper index = value + 1), Finset (Fin n), f : Fin m → Finset (Fin n) → ℝ; reason: Lean representation; same instances
--   - encoding: standing assumption of §4 (p.18): every component normalized, f_i(∅) = f_i([n]) = 0, nonnegative submodular → explicit hypotheses hf0, hsub, hempty, huniv; reason: the section's standing hypotheses written as binders; same instances
--   - generalization: the proof assumes F ≢ 0 (so that Σ_i p_i ≥ 1) before Step 4 → no such hypothesis; reason: when F ≡ 0 every p_i = 0, the event is empty and both bounds hold; the statement specializes to the source's case F ≢ 0
--   - encoding: N = |supp(w)| = Σ_i ξ_i → supportCard of the weight vector (number of nonzero w_i); reason: w_i ≠ 0 exactly when ξ_i = 1 and Λp_i > 0; ξ_i = 1 has probability 0 when Λp_i = 0
-- source:
--   Bao, Cai, Chen, He, Zhang, Nearly Optimal Submodular Sparsification, with and without Cardinality Constraints, arXiv:2606.20777 (version held, sha256 358242d6…), proof of Theorem 4.1, §4.3, Step 4, pp.27–28 (PDF pp.29–30)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SubmodSparsify_weights
import Definitions.Def_SubmodSparsify_bernProb

namespace SubmodSparsify

/-- **§4.3, Step 4** (pp.27–28): the support bound.

Bao, Cai, Chen, He, Zhang, *Nearly Optimal Submodular Sparsification, with and without
Cardinality Constraints*, arXiv:2606.20777 (version held), proof of Theorem 4.1, §4.3, Step 4, pp.27–28.

With `pᵢ` the weights of Algorithm 1, `ε, δ ∈ (0, 1)`, `Λ = 56ε⁻² log(32n/δ)` and
`N := |supp(w)|` the number of sampled components,
`Pr[N > 2ΛΣᵢ pᵢ] ≤ exp(−(2 log 2 − 1)ΛΣᵢ pᵢ)` and `Pr[N > 2ΛΣᵢ pᵢ] < δ/2`.

**Formalization Note.** `[n]` is `Fin n`, components `f : Fin m → Finset (Fin n) → ℝ`
(paper indices = values + 1), `S̄ = Sᶜ`. The hypotheses on `f` are those of Theorem 4.1, the
standing assumption of §4 (p.18): nonnegative, submodular, `fᵢ(∅) = fᵢ([n]) = 0`. `inShare f u i`
is `s_i^{(u)}`, `outShare f v i` is `t_i^{(v)}`, `weights f i` is `pᵢ`, `influence f S w` is
`inf_S(w)` of (25), `residual f i S U` is `Δᵢ(S, U)` of (24) (module `SubmodSparsify.weights`). The sample, its law and `w` are those of module `SubmodSparsify.bernProb` with
`Λ = samplingScale n ε δ`; `N` is `supportCard w`. The paper derives `< δ/2` from the exponential
bound and `Σᵢ pᵢ ≥ 1`, valid when `F ≢ 0`; when `F ≡ 0` all `pᵢ = 0` and the event is empty, so the
statement needs no `F ≢ 0` hypothesis. -/
theorem step_4_support {n m : ℕ} (f : Fin m → Finset (Fin n) → ℝ) (hf0 : ∀ i S, 0 ≤ f i S)
    (hsub : ∀ i, NonmonotoneSubmod.Shared.Submodular (f i))
    (hempty : ∀ i, f i ∅ = 0) (huniv : ∀ i, f i Finset.univ = 0)
    (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    bernProb (sampleProb (weights f) (samplingScale n ε δ)) (fun ξ =>
        2 * samplingScale n ε δ * ∑ i, weights f i <
          (supportCard (sampledWeight (weights f) (samplingScale n ε δ) ξ) : ℝ)) ≤
      Real.exp (-(2 * Real.log 2 - 1) * samplingScale n ε δ * ∑ i, weights f i) ∧
    bernProb (sampleProb (weights f) (samplingScale n ε δ)) (fun ξ =>
        2 * samplingScale n ε δ * ∑ i, weights f i <
          (supportCard (sampledWeight (weights f) (samplingScale n ε δ) ξ) : ℝ)) <
      δ / 2 := by sorry

end SubmodSparsify
