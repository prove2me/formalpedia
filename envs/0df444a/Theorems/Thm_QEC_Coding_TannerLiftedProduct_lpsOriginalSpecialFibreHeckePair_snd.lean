-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibreHeckePair_snd
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreHeckePair_snd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:08:43.742455+00:00
-- url     : https://prove2.me/theorems/437aa6ed-b4e0-4b10-b260-5bc51f35f8e6
-- title:
--   Tanner Lifted Product: lps Original Special Fibre Hecke Pair snd
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Special Fibre Hecke Pair snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialHecke.lean#L193-L199
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialHecke.lean#L193-L199

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialHecke
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open QEC.Coding.AlgebraicGeometry.SchemeFrobenius
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreHeckePair_snd
    (l N M : ℕ) [Fact l.Prime] [NeZero N] [NeZero M]
    (hNM : N ∣ M) (h4N : 4 ∣ N) (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalSpecialFibreHeckePair l N M hNM h4N hN hM ≫ pullback.snd
      (lpsOriginalSpecialFibreToPrimeField l N hN) (lpsOriginalSpecialFibreToPrimeField l N hN) =
    lpsOriginalSpecialFibreSecondLevelMap l N M hNM h4N hN hM := by sorry
