-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibreLift_isPullback
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreLift_isPullback
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:07:44.930208+00:00
-- url     : https://prove2.me/theorems/ddfeedc2-978b-4119-9933-b34cff812cc3
-- title:
--   Tanner Lifted Product: lps Original Special Fibre Lift is Pullback
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Special Fibre Lift is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialHecke.lean#L62-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialHecke.lean#L62-L79

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialHecke
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open QEC.Coding.AlgebraicGeometry.SchemeFrobenius
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreLift_isPullback (l N M : ℕ) [Fact l.Prime]
    (hN : 0 < N) (hM : 0 < M)
    (a : lpsOriginalIntegerNormalGluedScheme M hM ⟶ lpsOriginalIntegerNormalGluedScheme N hN)
    (ha : a ≫ lpsOriginalIntegerNormalGluedToSpecZ N hN =
      lpsOriginalIntegerNormalGluedToSpecZ M hM) :
    IsPullback (lpsOriginalSpecialFibreLift l N M hN hM a ha)
      (pullback.fst (lpsOriginalIntegerNormalGluedToSpecZ M hM) (lpsOriginalPrimeSpecToInteger l))
      (pullback.fst (lpsOriginalIntegerNormalGluedToSpecZ N hN) (lpsOriginalPrimeSpecToInteger l)) a := by sorry
