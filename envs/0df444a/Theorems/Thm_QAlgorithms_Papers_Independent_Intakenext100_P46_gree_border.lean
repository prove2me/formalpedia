-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P46_gree_border
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P46.gree_border
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:57:29.900994+00:00
-- url     : https://prove2.me/theorems/9ea81c5b-89e2-445c-bc7f-8a88f59f499d
-- title:
--   Theorem 2 / abstract headline: Gaussian REE is attained at a separability border
-- statement:
--   Let $\rho$ be an entangled Gaussian density operator on finitely many complete bosonic modes, with at least one mode at each party of a fixed bipartition. All separability statements mean trace-norm closed convex-hull separability. Write $D$ for extended Umegaki relative entropy with natural logarithms and $E_{GR}$ for its infimum over all separable Gaussian densities, with arbitrary means and no energy restriction. Then there exists such a density $\sigma$ with
--   $$D(\rho\Vert\sigma)=E_{GR}(\rho),$$
--   and its covariance lies on the separability border relative to physical Gaussian covariances: every covariance neighborhood at fixed mean contains an entangled Gaussian density. Pure normal modes are included. This gives both attainment and the Gaussian border restriction.
-- source:
--   Gaussian relative entropy of entanglement, arXiv:quant-ph/0402109v3, PDF p. 4, Theorem 2 / abstract headline: Gaussian REE is attained at a separability border

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P46

open scoped BigOperators ENNReal ComplexOrder Matrix

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsSeparable)

open QAlgorithms.Papers.Independent.Dependency50.P13
  (finiteRelativeEntropy compression entropyWeight)

open QAlgorithms.Papers.Independent.Claimed50.P47
  (Occupation bipartiteCharacteristic bipartiteWeyl gaussianStateCharacteristic)

-- These accepted definitions have the same completed Hilbert-space meaning.

open QAlgorithms.Papers.Independent.Next46.P13 (coordinateBasis)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

open QAlgorithms.Papers.Independent.Claimed50.P41 (IsDiagonal)

/-- Chen, Theorem 2, PDF pp.4–6 (abstract p.1): Gaussian REE is attained
at a covariance border on the same nontrivial cut. Singular densities remain. -/
theorem gree_border {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (rho : State (Occupation A × Occupation B))
    (hgaussian : IsGaussianDensity rho) (hentangled : ¬ IsSeparable rho.coefficients) :
    ∃ sigma : State (Occupation A × Occupation B), GaussianBorder sigma ∧
      operatorRelativeEntropy rho sigma = gree rho := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P46

end
