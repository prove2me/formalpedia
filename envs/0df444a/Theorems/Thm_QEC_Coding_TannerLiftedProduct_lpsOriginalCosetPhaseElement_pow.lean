-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCosetPhaseElement_pow
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCosetPhaseElement_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:12:26.78819+00:00
-- url     : https://prove2.me/theorems/14a86067-fb5f-47dd-b8d9-c71bc9ced262
-- title:
--   Tanner Lifted Product: lps Original Coset Phase Element pow
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Coset Phase Element pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspPhaseResidue.lean#L379-L383
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspPhaseResidue.lean#L379-L383

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCosetPhaseElement_pow
    (N : ℕ) (hN : 0 < N) (x : LPSOriginalCuspIndex N) :
    (lpsOriginalCosetPhaseElement N hN x)^N = 1 := by sorry
