-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspJNumerator_constant
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspJNumerator_constant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:13:01.011776+00:00
-- url     : https://prove2.me/theorems/f4d9c005-97d7-4a88-94ce-f1da3d44f335
-- title:
--   Tanner Lifted Product: lps Original Cusp JNumerator constant
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Cusp JNumerator constant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCosetCuspSeries.lean#L29-L33
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCosetCuspSeries.lean#L29-L33

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspPhaseResidue
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCosetCuspSeries
set_option autoImplicit false
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] lpsOriginalLevelPhaseResidue_field

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspJNumerator_constant (R : Type*) [CommRing R] :
    PowerSeries.constantCoeff (lpsOriginalCuspJNumerator R) = 1 := by sorry
