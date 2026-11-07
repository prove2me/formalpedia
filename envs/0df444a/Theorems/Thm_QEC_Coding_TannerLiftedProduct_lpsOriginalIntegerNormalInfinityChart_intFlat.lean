-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalInfinityChart_intFlat
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalInfinityChart_intFlat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:03:49.330326+00:00
-- url     : https://prove2.me/theorems/7f3fc64e-271a-4093-bbfc-d159f07153e6
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Infinity Chart int Flat
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Infinity Chart int Flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerFlatModel.lean#L31-L36
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerFlatModel.lean#L31-L36

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerFlatModel
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalInfinityChart_intFlat (N : ℕ) (hN : 0 < N) :
    (Int.castRingHom (lpsOriginalIntegerNormalInfinityChart N hN)).Flat := by sorry
