-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLevelPhaseResidue_charP
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalLevelPhaseResidue_charP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:12:04.009338+00:00
-- url     : https://prove2.me/theorems/c577b6a3-aa91-4c1f-b5e3-9e4b095594aa
-- title:
--   Tanner Lifted Product: lps Original Level Phase Residue char P
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Level Phase Residue char P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspPhaseResidue.lean#L318-L330
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspPhaseResidue.lean#L318-L330

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalLevelPhaseResidue_charP
    (N : ℕ) (hN : 0 < N) (p : ℕ) (hp : p.Prime) :
    CharP (LPSOriginalLevelPhaseResidue N hN p hp) p := by sorry
