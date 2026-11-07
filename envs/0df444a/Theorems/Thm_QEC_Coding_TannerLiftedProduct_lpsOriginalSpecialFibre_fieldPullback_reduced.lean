-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibre_fieldPullback_reduced
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibre_fieldPullback_reduced
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T04:35:17.529353+00:00
-- url     : https://prove2.me/theorems/ecd72eb2-433b-4f63-bd11-24ff582d4d61
-- title:
--   Tanner Lifted Product: lps Original Special Fibre field Pullback reduced
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Special Fibre field Pullback reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGeometricallyReducedSpecialFiber.lean#L30-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGeometricallyReducedSpecialFiber.lean#L30-L37

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeReducedBaseChange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReducedSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGeometricallyReducedSpecialFiber
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibre_fieldPullback_reduced
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 0 < N)
    (hpN : ¬ p ∣ N) (K : Type) [Field K]
    (g : Spec (.of K) ⟶ Spec (.of (ZMod p))) :
    _root_.AlgebraicGeometry.IsReduced
      (pullback (lpsOriginalSpecialFibreToPrimeField p N hN) g) := by sorry
