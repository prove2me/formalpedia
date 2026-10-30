-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P27_corollary33
-- name    : QAlgorithms.Papers.Independent.Extend50.P27.corollary33
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:57:46.331532+00:00
-- url     : https://prove2.me/theorems/ee83c0e0-03c6-4f3c-a68c-6a84e96db51f
-- title:
--   Corollary 33: coefficient translation for spectral measurement filters
-- statement:
--   Use $N\ge1$, $d\ge2$, physical diagrams $\alpha\vdash N-1$, $\mu\vdash N$, and one-box compatibility $\mu\in\alpha$. Let $d_\lambda$ and $m_\lambda$ be the actual Specht dimensions and tensor-permutation multiplicities. The operators $F_\mu(\alpha)$ are constructed by Eq. (145), and $\lambda_\mu(\alpha)=N m_\mu d_\alpha/(d^N m_\alpha d_\mu)>0$. All sums below use compatible physical labels. Write $\rho_\alpha^t=\sum_{\mu\in\alpha}\lambda_\mu(\alpha)^tF_\mu(\alpha)$, extended by zero off its support.
--
--   Let $z_\alpha\ge0$ and $y_\alpha\in\mathbb R\setminus\{0\}$. The filter $\sum_{\alpha,\mu\in\alpha}p_\mu(\alpha)F_\mu(\alpha)$ equals $\sum_\alpha\sqrt{z_\alpha}\rho_\alpha^{-1/y_\alpha}$ exactly when its compatible coefficients satisfy
--
--   $$p_\mu(\alpha)=\sqrt{z_\alpha}\lambda_\mu(\alpha)^{-1/y_\alpha}.$$
--
--   These coefficients give $\Pi\sigma_a\Pi=\sum_\alpha z_\alpha\rho_\alpha^{-1/y_\alpha}\sigma_a(\alpha)\rho_\alpha^{-1/y_\alpha}$, where the block signals are the transported $P_\alpha\otimes\widetilde P^+$ seeds divided by $d^N$. This is a coefficient and operator identity; it asserts neither feasibility nor optimality for arbitrary parameters.
-- source:
--   Optimal Port-based Teleportation, arXiv:1707.08456v1, PDF p. 24, Corollary 33: coefficient translation for spectral measurement filters

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P27

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

open QAlgorithms.Schur

namespace QAlgorithms.Papers.Independent.Extend50.P27

open QAlgorithms.Papers.Independent.Renew46.P26 (deleteLast)

open QAlgorithms.Papers.Independent.Gap20.P01 (spechtMatrix)

open QAlgorithms.Papers.Independent.Claimed50.P28 (traceInput)

attribute [local instance] Classical.propDecidable

/-- Corollary 33, Eq.(111), with sqrt(z) multiplying lambda^(-1/y)
(PDF p.24). This identifies filters and effects, not optimality of arbitrary z,y.
Coefficients outside one-box compatibility do not contribute. -/
theorem corollary33 {d K : ℕ} (hd : 2 ≤ d) (z y : Partition d K → ℝ)
    (hz : ∀ alpha, 0 ≤ z alpha) (hy : ∀ alpha, y alpha ≠ 0)
    (p : Partition d K → Partition d (K+1) → ℝ)
    (hp : ∀ alpha mu, Predecessor alpha.val mu.val → 0 ≤ p alpha mu) :
    (coefficientFilter p =
      ∑ alpha : Partition d K, (Real.sqrt (z alpha) : ℂ) • blockPower alpha (-(y alpha)⁻¹) ↔
      ∀ alpha mu, Predecessor alpha.val mu.val →
        p alpha mu = Real.sqrt (z alpha) * Real.rpow (lambdaValue alpha mu) (-(y alpha)⁻¹)) ∧
    (filterEffects (coefficientFilter (fun alpha mu =>
      Real.sqrt (z alpha) * Real.rpow (lambdaValue alpha mu) (-(y alpha)⁻¹))) = powerEffects z y) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P27

end
