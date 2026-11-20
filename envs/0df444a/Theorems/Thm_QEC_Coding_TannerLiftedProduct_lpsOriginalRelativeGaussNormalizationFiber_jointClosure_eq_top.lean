-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationFiber_jointClosure_eq_top
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationFiber_jointClosure_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T11:52:02.704755+00:00
-- url     : https://prove2.me/theorems/d772a86d-387b-422e-a09b-3c5a511d0f16
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Normalization Fiber joint Closure eq top
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Normalization Fiber joint Closure eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussJointFiber.lean#L76-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussJointFiber.lean#L76-L117

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusFiber
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointFiber
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationFiber_jointClosure_eq_top
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    Subring.closure
      (Set.range (lpsOriginalRelativeGaussNormalizationFirstFiberMap N p hNp h4N hN hpN q) ∪
        Set.range (lpsOriginalRelativeGaussNormalizationSecondFiberMap N p hNp h4N hN hpN q)) = ⊤ := by sorry
