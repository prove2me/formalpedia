-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerPolynomial_actualCosetTaylorProduct
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerPolynomial_actualCosetTaylorProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:23:26.648202+00:00
-- url     : https://prove2.me/theorems/9d73a33d-369e-4ffb-b498-5471199148b7
-- title:
--   Tanner Lifted Product: lps Original Integer Polynomial actual Coset Taylor Product
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Polynomial actual Coset Taylor Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCoprimeModularReduction.lean#L88-L123
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCoprimeModularReduction.lean#L88-L123

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerPolynomial_actualCosetTaylorProduct
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := Fintype.ofFinite (LPSOriginalCuspIndex N)
    ((lpsOriginalIntegerPolynomial N hN).map
      (lpsOriginalAnalyticLevelCoefficientEval N hN)).map
        lpsOriginalAnalyticCuspLocalizedTaylor =
      ∏ x : LPSOriginalCuspIndex N, (Polynomial.X - Polynomial.C
        (lpsOriginalAnalyticCuspLocalizedTaylor (lpsOriginalAnalyticCosetBranch N hN x))) := by sorry
