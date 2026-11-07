-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCosetCuspData_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCosetCuspData_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:16:54.89319+00:00
-- url     : https://prove2.me/theorems/9df38eb2-2cb0-442c-acfa-df89e830dd12
-- title:
--   Tanner Lifted Product: lps Original Coset Cusp Data injective
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Coset Cusp Data injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspPhaseResidue.lean#L217-L250
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspPhaseResidue.lean#L217-L250

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.KummerExtension
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspPhaseResidue
set_option autoImplicit false
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCosetCuspData_injective
    (N : ℕ) (hN : 0 < N) :
    Function.Injective (lpsOriginalCosetCuspData N hN) := by sorry
