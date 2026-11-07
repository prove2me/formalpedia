-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerPolynomial_pointwiseProduct
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerPolynomial_pointwiseProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:23:25.362199+00:00
-- url     : https://prove2.me/theorems/033a3d0d-dd9c-43b1-8e35-a12f94bbf964
-- title:
--   Tanner Lifted Product: lps Original Integer Polynomial pointwise Product
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Polynomial pointwise Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCoprimeModularReduction.lean#L28-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCoprimeModularReduction.lean#L28-L56

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCosetCuspSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCoprimeModularReduction
set_option autoImplicit false
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] lpsOriginalLevelPhaseResidue_field

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerPolynomial_pointwiseProduct
    (N : ℕ) [NeZero N] (hN : 0 < N) (τ : ℍ) :
    letI := Fintype.ofFinite (LPSOriginalCuspIndex N)
    (lpsOriginalIntegerPolynomial N hN).map
      ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (Int.castRingHom ℂ))) =
      ∏ x : LPSOriginalCuspIndex N,
        (Polynomial.X - Polynomial.C (lpsOriginalJDilated N hN (x.out.val⁻¹ • τ))) := by sorry
