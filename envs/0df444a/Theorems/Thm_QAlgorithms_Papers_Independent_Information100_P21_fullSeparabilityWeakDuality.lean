-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_fullSeparabilityWeakDuality
-- name    : QAlgorithms.Papers.Independent.Information100.P21.fullSeparabilityWeakDuality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:14:36.802281+00:00
-- url     : https://prove2.me/theorems/4e1cadf8-d99c-4bed-9d78-880a4ba40698
-- title:
--   X — witness lower bounds relative to full separability
-- statement:
--   Let $\rho$ be a finite multipartite density operator and $Z$ Hermitian. If $0\le\operatorname{Tr}(Z\sigma)\le1$ for every fully separable $\sigma$, then
--   $$R_s^{\mathrm{FS}}(\rho)\ge-\operatorname{Tr}(Z\rho).$$
--   If instead $Z$ is nonnegative on the free set and $Z\preceq I$, the same bound holds for generalized robustness. Every admissible identity $\rho+t\tau=(1+t)\sigma$ has $t\ge-\operatorname{Tr}(Z\rho)$, with fully separable standard noise or arbitrary density-operator generalized noise.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 28, X — witness lower bounds relative to full separability

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 28, witness lower bounds relative to full separability. -/
theorem fullSeparabilityWeakDuality {P : Type*} [Fintype P] (d : P → ℕ) (hd : ∀ j,0<d j)
  (rho Z : Op (Config d)) (hr : QAlgorithms.IsDensityMatrix rho) (hZ : Z.IsHermitian) :
  ((∀ sigma : Op (Config d), sigma∈fs d → 0≤(Z*sigma).trace.re ∧ (Z*sigma).trace.re≤1) →
    -(Z*rho).trace.re≤fsR d true rho ∧
    ∀ (t : ℝ) (tau sigma : Op (Config d)), 0≤t → tau∈fs d → sigma∈fs d →
      rho+(t:ℂ) • tau=(1+t:ℂ) • sigma → -(Z*rho).trace.re≤t) ∧
  (((∀ sigma : Op (Config d), sigma∈fs d → 0≤(Z*sigma).trace.re) ∧ (1-Z).PosSemidef) →
    -(Z*rho).trace.re≤fsR d false rho ∧
    ∀ (t : ℝ) (tau sigma : Op (Config d)), 0≤t → QAlgorithms.IsDensityMatrix tau → sigma∈fs d →
      rho+(t:ℂ) • tau=(1+t:ℂ) • sigma → -(Z*rho).trace.re≤t) := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
