-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimePullback_isReduced_of_quotient
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimePullback_isReduced_of_quotient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:32:46.579899+00:00
-- url     : https://prove2.me/theorems/51e0d07d-128f-4d78-850b-b686332924b5
-- title:
--   Tanner Lifted Product: lps Original Prime Pullback is Reduced of quotient
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Prime Pullback is Reduced of quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReducedSpecialFiber.lean#L50-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReducedSpecialFiber.lean#L50-L62

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReducedSpecialFiber
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimePullback_isReduced_of_quotient
    (C : Type) [CommRing C] (p : ℕ) [Fact p.Prime]
    (h : _root_.IsReduced (C ⧸ Ideal.span {(p : C)}))
    (f : Spec (.of C) ⟶ Spec (.of ℤ)) :
    _root_.AlgebraicGeometry.IsReduced (pullback f (lpsOriginalPrimeSpecToInteger p)) := by sorry
