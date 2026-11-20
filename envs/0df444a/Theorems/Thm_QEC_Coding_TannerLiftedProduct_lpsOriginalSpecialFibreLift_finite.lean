-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibreLift_finite
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreLift_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:07:20.483464+00:00
-- url     : https://prove2.me/theorems/df734ca2-6214-4bca-a47b-e8bce2007770
-- title:
--   Tanner Lifted Product: lps Original Special Fibre Lift finite
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Special Fibre Lift finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialHecke.lean#L81-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialHecke.lean#L81-L88

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialHecke
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open QEC.Coding.AlgebraicGeometry.SchemeFrobenius
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreLift_finite (l N M : ℕ) [Fact l.Prime]
    (hN : 0 < N) (hM : 0 < M)
    (a : lpsOriginalIntegerNormalGluedScheme M hM ⟶ lpsOriginalIntegerNormalGluedScheme N hN)
    (ha : a ≫ lpsOriginalIntegerNormalGluedToSpecZ N hN =
      lpsOriginalIntegerNormalGluedToSpecZ M hM) (hf : IsFinite a) :
    IsFinite (lpsOriginalSpecialFibreLift l N M hN hM a ha) := by sorry
