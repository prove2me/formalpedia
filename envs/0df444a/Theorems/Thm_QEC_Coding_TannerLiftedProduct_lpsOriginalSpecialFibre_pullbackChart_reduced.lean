-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibre_pullbackChart_reduced
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibre_pullbackChart_reduced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:33:55.364961+00:00
-- url     : https://prove2.me/theorems/b87dbf9b-40aa-4e76-a447-98e9cc414945
-- title:
--   Tanner Lifted Product: lps Original Special Fibre pullback Chart reduced
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Special Fibre pullback Chart reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReducedSpecialFiber.lean#L64-L86
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReducedSpecialFiber.lean#L64-L86

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibre_pullbackChart_reduced
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (hpN : ¬ p ∣ N) (b : Bool) :
    _root_.AlgebraicGeometry.IsReduced
      (pullback (lpsOriginalIntegerNormalGluedChartMap N hN b)
        (pullback.fst (lpsOriginalIntegerNormalGluedToSpecZ N hN)
          (lpsOriginalPrimeSpecToInteger p))) := by sorry
