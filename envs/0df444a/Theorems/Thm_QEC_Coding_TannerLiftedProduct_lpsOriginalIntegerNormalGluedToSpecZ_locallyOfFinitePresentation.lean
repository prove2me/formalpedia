-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedToSpecZ_locallyOfFinitePresentation
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedToSpecZ_locallyOfFinitePresentation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:05:53.022692+00:00
-- url     : https://prove2.me/theorems/8b35af96-3662-4f3e-81df-d927a7cf4233
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Glued To Spec Z locally Of Finite Presentation
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Glued To Spec Z locally Of Finite Presentation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerFlatModel.lean#L153-L157
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerFlatModel.lean#L153-L157

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerFlatModel
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedToSpecZ_locallyOfFinitePresentation
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    LocallyOfFinitePresentation (lpsOriginalIntegerNormalGluedToSpecZ N hN) := by sorry
