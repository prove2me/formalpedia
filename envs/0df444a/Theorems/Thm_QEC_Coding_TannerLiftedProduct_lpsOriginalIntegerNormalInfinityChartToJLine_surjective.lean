-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalInfinityChartToJLine_surjective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalInfinityChartToJLine_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:05:02.728357+00:00
-- url     : https://prove2.me/theorems/f4caa18c-9fbf-4972-a45e-8ba3a3e91a60
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Infinity Chart To JLine surjective
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Infinity Chart To JLine surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerFlatModel.lean#L90-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerFlatModel.lean#L90-L113

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerFlatModel
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalInfinityChartToJLine_surjective
    (N : ℕ) (hN : 0 < N) :
    Surjective (lpsOriginalIntegerNormalInfinityChartToJLine N hN) := by sorry
