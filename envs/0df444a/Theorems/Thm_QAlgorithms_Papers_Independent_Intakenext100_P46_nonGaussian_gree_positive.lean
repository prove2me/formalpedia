-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P46_nonGaussian_gree_positive
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P46.nonGaussian_gree_positive
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:07:55.161247+00:00
-- url     : https://prove2.me/theorems/0d5ba7a1-cb9c-46eb-a9d0-b73dff8bdfc6
-- title:
--   §6: non-Gaussian extension of GREE and strict nonzero value
-- statement:
--   Let $\rho$ be any non-Gaussian density operator on finitely many complete bosonic modes on a fixed bipartition with at least one mode per party. There is no finite-energy or finite-moment assumption on $\rho$. Define its extended Gaussian relative entropy of entanglement using all separable Gaussian density operators on the same cut. Then
--   $$E_{GR}(\rho):=\inf_{\sigma\ \mathrm{separable\ Gaussian}}D(\rho\Vert\sigma)>0.$$
--   Here $D$ is the independently defined extended Umegaki divergence in nats, and separability means trace-norm closed convex-hull separability. The strict inequality concerns the infimum itself, which may be infinite. This records the deficiency noted for the extension to non-Gaussian inputs.
-- source:
--   Gaussian relative entropy of entanglement, arXiv:quant-ph/0402109v3, PDF p. 12, §6: non-Gaussian extension of GREE and strict nonzero value

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

/-- Chen, PDF p.12: extended GREE of a non-Gaussian density is strictly
nonzero. No finite-energy or finite-moment hypothesis is added to rho. -/
theorem nonGaussian_gree_positive {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (rho : State (Occupation A × Occupation B))
    (hnongaussian : ¬ IsGaussianDensity rho) : 0 < gree rho := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P46

end
