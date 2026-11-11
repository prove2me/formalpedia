-- Prove2me | Theorems.Thm_SparseTensorInj_Certify_proposition_36
-- name    : SparseTensorInj.Certify.proposition_36
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:38:03.398177+00:00
-- url     : https://prove2.me/theorems/6f001f12-d182-4e5e-9f7f-61f59b0f66a0
-- title:
--   Proposition 36 — the even-order case of Theorem 5: $\|A(T)\|_{\mathrm{op}}$ certifies $C_q(\sigma n^{q/2}+\gamma\sqrt{\log(1+\gamma^2/\sigma^2)}\sqrt{\log n})$
-- statement:
--   Fix an integer $q\ge1$ and let $u(T)=\|A(T)\|_{\mathrm{op}}$ be the operator norm of the balanced flattening of an order-$2q$ tensor (Definition 37). Then:
--
--   1. (correctness) $u(T)\ge\|T\|_{\mathrm{inj}}$ for every $n$ and every symmetric order-$2q$ tensor $T$ over $\mathbb R^n$;
--   2. (utility) there are $C_q>0$ and $\delta:\mathbb N\to\mathbb R$ with $\delta(n)\to0$, depending only on $q$, such that for every $n\ge2q$, every $\sigma,\gamma>0$ and every coefficient family of Definition 3, the random tensor $T$ satisfies
--   $$\Pr\Big[u(T)>C_q\Big(\sigma n^{q/2}+\gamma\sqrt{\log(1+\gamma^2/\sigma^2)}\sqrt{\log n}\Big)\Big]\le\delta(n).$$
--
--   This is the even half of Theorem 5 ($k=2q$, $n^{q/2}=n^{k/4}$).
--
--   Differences from the source:
--
--   - reading: there exists a polynomial-time certification algorithm → the paper's explicit certificate (‖A(T)‖_op of Definition 37 for even order, eq. (9) for odd order) is correct for every symmetric tensor and has the stated utility; reason: running time is not modelled; an existential certificate without a running-time bound is trivial (u = ‖T‖_inj); the paper proves this certificate polynomial-time computable (p. 24, p. 54)
--   - reading: with probability 1 − o_n(1) (with high probability), C_k > 0 depending only on k → ∃ C > 0, ∃ δ : ℕ → ℝ with δ n → 0, both chosen before n, σ, γ, the probability space and the law of χ, such that P{C · b < u(T)} ≤ δ n for every n ≥ k; reason: the uniform reading is the stronger one; the paper uses it (Corollary 8 takes p = p(n)) and proves it (failure probability O_q(n^{-3}), resp. n^{-5} + n^{-6}, independent of σ, γ and the law)
--   - encoding: ‖T‖_inj = max over unit vectors x of |⟨T, x^{⊗k}⟩| → the real supremum ⨆ over {x : Fin n → ℝ | Σ x_i² = 1}; reason: the set of values is bounded and the maximum is attained for n ≥ 1; for n = 0 (empty sphere) the value is 0 and the claim is trivial
--   - encoding: indices in [n] = {1,…,n}; the k-element subsets [n]_k → Fin n (0-based); KSubset n k = {e : Finset (Fin n) // e.card = k}; reason: relabelling of the index set; same instances
--   - encoding: ‖χ‖_ψ2 ≤ γ, with ‖χ‖_ψ2 = inf{t > 0 : E exp(χ²/t²) ≤ 2} → Psi2Le P χ γ: exp(χ²/γ²) is integrable and E exp(χ²/γ²) ≤ 2 (with γ > 0); reason: for γ > 0 the two are equivalent: t ↦ E exp(χ²/t²) is non-increasing and right-continuous by monotone convergence
--   - encoding: random variables on an unspecified probability space → every probability space (Ω : Type, P) with IsProbabilityMeasure P; reason: any joint law of finitely many real variables is realized on such a space; Lean universe convention
-- source:
--   Kothari, Louis, Paul, Raghavendra, Improved Bounds for Certifying Injective Norm of Sparse Random Tensors, STOC 2027 submission (manuscript of November 3, 2026, sha256 e46cf53d…), p. 22, Proposition 36 (proof p. 24)

import Mathlib
import Definitions.Def_SparseTensorInj_Certify_RandomModel
import Definitions.Def_SparseTensorInj_Certify_EvenCertificate

open MeasureTheory ProbabilityTheory Filter Topology

namespace SparseTensorInj.Certify

/-- Proposition 36 (p. 22), the even case `k = 2q` of Theorem 5, for the certificate
`u(T) = ‖A(T)‖_op` of Definition 37: (correctness) `u(T) ≥ ‖T‖_inj` for every symmetric
order-`2q` tensor; (utility) there are `C_q > 0` and `δ_n → 0`, depending only on `q`, such that
for every `n ≥ 2q`, every `σ, γ > 0` and every coefficient family of Definition 3,
`Pr[u(T) > C_q (σ n^{q/2} + γ √(log(1 + γ^2/σ^2)) √(log n))] ≤ δ_n`. -/
theorem proposition_36 (q : ℕ) (hq : 1 ≤ q) :
    (∀ (n : ℕ) (T : Tensor (q + q) n), IsSymmetric T → injNorm T ≤ evenCert T) ∧
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
      ∀ (n : ℕ), q + q ≤ n →
      ∀ (σ γ : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (χ : KSubset n (q + q) → Ω → ℝ),
        IsSubgaussianFamily P χ σ γ →
        P {ω | C * (σ * (n : ℝ) ^ ((q : ℝ) / 2) +
            γ * Real.sqrt (Real.log (1 + γ ^ 2 / σ ^ 2)) * Real.sqrt (Real.log n)) <
            evenCert (modelTensor χ ω)} ≤ ENNReal.ofReal (δ n) := by sorry

end SparseTensorInj.Certify
