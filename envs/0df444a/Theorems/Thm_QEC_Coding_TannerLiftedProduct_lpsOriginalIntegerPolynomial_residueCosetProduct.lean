-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerPolynomial_residueCosetProduct
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerPolynomial_residueCosetProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:25:25.088107+00:00
-- url     : https://prove2.me/theorems/d13becec-c6dc-46de-b44e-6a99a95f2bed
-- title:
--   Tanner Lifted Product: lps Original Integer Polynomial residue Coset Product
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Polynomial residue Coset Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCoprimeModularReduction.lean#L214-L229
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCoprimeModularReduction.lean#L214-L229

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerPolynomial_residueCosetProduct
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) (hp : p.Prime) :
    letI := Fintype.ofFinite (LPSOriginalCuspIndex N)
    (lpsOriginalIntegerPolynomial N hN).map
      (lpsOriginalResidueLevelCoefficientEval N hN p hp) =
      ∏ x : LPSOriginalCuspIndex N,
        (Polynomial.X - Polynomial.C (lpsOriginalCosetResidueCuspSeries N hN p hp x)) := by sorry
