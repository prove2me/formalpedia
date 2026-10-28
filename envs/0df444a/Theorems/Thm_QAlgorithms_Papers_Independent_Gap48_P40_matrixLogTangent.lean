-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P40_matrixLogTangent
-- name    : QAlgorithms.Papers.Independent.Gap48.P40.matrixLogTangent
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T05:20:35.30503+00:00
-- url     : https://prove2.me/theorems/4ec53f36-260d-47ae-81f6-9c3ead41476b
-- title:
--   §V.A, Lemma 6: matrix logarithm tangent bound
-- statement:
--   Let $A$ be a positive definite matrix in positive finite dimension and let $H=H^*$ satisfy $A+H>0$. The following matrix integral is integrable and obeys the Loewner inequality
--
--   $$
--   \log(A+H)-\log A\le\int_0^\infty(A+xI)^{-1}H(A+xI)^{-1}\,dx.
--   $$
--
--   This is the supporting tangent inequality for the matrix logarithm.
-- source:
--   Continuity bounds on the quantum relative entropy, arXiv:quant-ph/0503218v3, PDF p. 4, §V.A, Lemma 6: matrix logarithm tangent bound

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.L2Operator

open Filter MeasureTheory Asymptotics

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

namespace QAlgorithms.Papers.Independent.Gap48.P40

/-- PDF p.4, Lemma 6: the tangent inequality in Loewner order. Integrability
is asserted, so no Bochner-integral default or extra integrability premise is used. -/
theorem matrixLogTangent {d : ℕ} (hd : 0 < d) (A D : Mat d)
    (hA : A.PosDef) (hD : D.IsHermitian) (hAD : (A + D).PosDef) :
    Integrable (fun x : ℝ => (A + (x : ℂ) • (1 : Mat d))⁻¹ * D *
      (A + (x : ℂ) • (1 : Mat d))⁻¹) (volume.restrict (Set.Ioi 0)) ∧
    ((∫ x : ℝ in Set.Ioi 0, (A + (x : ℂ) • (1 : Mat d))⁻¹ * D *
      (A + (x : ℂ) • (1 : Mat d))⁻¹) -
      (cfc Real.log (A + D) - cfc Real.log A)).PosSemidef := by sorry

end QAlgorithms.Papers.Independent.Gap48.P40

end
