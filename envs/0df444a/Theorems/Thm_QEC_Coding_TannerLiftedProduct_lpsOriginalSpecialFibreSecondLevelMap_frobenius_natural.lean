-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibreSecondLevelMap_frobenius_natural
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreSecondLevelMap_frobenius_natural
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:08:09.324581+00:00
-- url     : https://prove2.me/theorems/0b7c1e55-d559-40ec-9e59-f6c98fec8c5b
-- title:
--   Tanner Lifted Product: lps Original Special Fibre Second Level Map frobenius natural
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Special Fibre Second Level Map frobenius natural property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialHecke.lean#L215-L222
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialHecke.lean#L215-L222

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialHecke
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open QEC.Coding.AlgebraicGeometry.SchemeFrobenius
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreSecondLevelMap_frobenius_natural
    (l N M : ℕ) [Fact l.Prime] [NeZero N] [NeZero M]
    (hNM : N ∣ M) (h4N : 4 ∣ N) (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalSpecialFibreFrobenius l M hM ≫
      lpsOriginalSpecialFibreSecondLevelMap l N M hNM h4N hN hM =
    lpsOriginalSpecialFibreSecondLevelMap l N M hNM h4N hN hM ≫
      lpsOriginalSpecialFibreFrobenius l N hN := by sorry
