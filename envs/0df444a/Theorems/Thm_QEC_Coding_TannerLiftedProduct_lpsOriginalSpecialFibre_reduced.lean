-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibre_reduced
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibre_reduced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:33:42.837821+00:00
-- url     : https://prove2.me/theorems/055919b8-9e87-4e31-acd1-c34bd9aaf5ef
-- title:
--   Tanner Lifted Product: lps Original Special Fibre reduced
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Special Fibre reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReducedSpecialFiber.lean#L88-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReducedSpecialFiber.lean#L88-L102

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibre_reduced
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (hpN : ¬ p ∣ N) : _root_.AlgebraicGeometry.IsReduced (lpsOriginalSpecialFibre p N hN) := by sorry
