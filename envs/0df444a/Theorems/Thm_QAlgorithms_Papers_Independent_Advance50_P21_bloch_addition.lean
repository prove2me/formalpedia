-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P21_bloch_addition
-- name    : QAlgorithms.Papers.Independent.Advance50.P21.bloch_addition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:54:25.17807+00:00
-- url     : https://prove2.me/theorems/3670f962-4352-409f-9bc6-0faf2ec52cb5
-- title:
--   Unnumbered qubit example: Bloch-vector addition (4.18)
-- statement:
--   Let $d=2$, let $\rho,\sigma$ be positive semidefinite complex $d\times d$ matrices of trace one, and let $a\in[0,1]$. Write
--   $$
--   \rho\boxplus_a\sigma=a\rho+(1-a)\sigma-i\sqrt{a(1-a)}(\rho\sigma-\sigma\rho).
--   $$
--
--   In the Pauli order $X,Y,Z$, the Bloch vector $r(\tau)\in\mathbb R^3$ is specified by $\tau=(I+r(\tau)\cdot\boldsymbol\sigma)/2$. Then
--   $$r(\rho\boxplus_a\sigma)=a r(\rho)+(1-a)r(\sigma)+\sqrt{a(1-a)}\,r(\rho)\times r(\sigma).$$
--   The cross product is right handed and lengths use the Euclidean norm. This is the coordinate form of qubit addition.
-- source:
--   Entropy power inequalities for qudits, arXiv:1503.04213v3, PDF p. 10, Unnumbered qubit example: Bloch-vector addition (4.18)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P21

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

open QAlgorithms.Papers.Independent.Dependency50.P16 (simplex orderedSpectrum majorizedBy)

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble)

open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P11 (thermalEntropyInverse)

/-- PDF p.10, (4.18), repeated p.33, (A.8): positive right-handed cross-product term. -/
theorem bloch_addition (rho sigma : Mat 2)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    qubitBlochVector (quditAddition a rho sigma) = a • qubitBlochVector rho + (1 - a) • qubitBlochVector sigma +
      Real.sqrt (a * (1 - a)) • blochCross (qubitBlochVector rho) (qubitBlochVector sigma) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P21

end
