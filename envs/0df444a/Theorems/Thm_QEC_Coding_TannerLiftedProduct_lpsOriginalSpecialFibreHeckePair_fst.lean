-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibreHeckePair_fst
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreHeckePair_fst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:08:31.069223+00:00
-- url     : https://prove2.me/theorems/3315818d-cdb6-4069-ba5f-61bd2930abf6
-- title:
--   Tanner Lifted Product: lps Original Special Fibre Hecke Pair fst
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Special Fibre Hecke Pair fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialHecke.lean#L185-L191
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialHecke.lean#L185-L191

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialHecke
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open QEC.Coding.AlgebraicGeometry.SchemeFrobenius
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreHeckePair_fst
    (l N M : ℕ) [Fact l.Prime] [NeZero N] [NeZero M]
    (hNM : N ∣ M) (h4N : 4 ∣ N) (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalSpecialFibreHeckePair l N M hNM h4N hN hM ≫ pullback.fst
      (lpsOriginalSpecialFibreToPrimeField l N hN) (lpsOriginalSpecialFibreToPrimeField l N hN) =
    lpsOriginalSpecialFibreForgetLevel l N M hNM h4N hN hM := by sorry
