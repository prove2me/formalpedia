-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLevelPrimitivePhase_isPrimitive
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalLevelPrimitivePhase_isPrimitive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:10:51.472793+00:00
-- url     : https://prove2.me/theorems/4aa090ec-47ff-4712-ad47-fdd2911c5251
-- title:
--   Tanner Lifted Product: lps Original Level Primitive Phase is Primitive
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Level Primitive Phase is Primitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspPhaseResidue.lean#L337-L342
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspPhaseResidue.lean#L337-L342

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.KummerExtension
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspPhaseResidue
set_option autoImplicit false
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalLevelPhaseResidue_field

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalLevelPrimitivePhase_isPrimitive (N : ℕ) (hN : 0 < N) :
    IsPrimitiveRoot (lpsOriginalLevelPrimitivePhase N hN) N := by sorry
