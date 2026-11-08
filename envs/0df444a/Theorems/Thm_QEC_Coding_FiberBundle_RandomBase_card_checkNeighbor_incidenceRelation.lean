-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_card_checkNeighbor_incidenceRelation
-- name    : QEC.Coding.FiberBundle.RandomBase.card_checkNeighbor_incidenceRelation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:04:25.334933+00:00
-- url     : https://prove2.me/theorems/05c20ad5-d388-4b0b-839d-199d94b30821
-- title:
--   Random Base: card check Neighbor incidence Relation
-- statement:
--   The Random Base construction uses the card check Neighbor incidence Relation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReduction.lean#L5514-L5520
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReduction.lean#L5514-L5520

import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialCode
import Definitions.Def_QEC_Coding_FiberBundle_WeightReduction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
open QEC.Coding.FiberBundle.RandomBase

theorem QEC.Coding.FiberBundle.RandomBase.card_checkNeighbor_incidenceRelation
    {r : Nat} (sample : Sample r) (a : Fin (3 * r)) :
    Fintype.card
        (ClassicalWeightReduction.CheckNeighbor
          (incidenceRelation sample) a) =
      checkDegree sample a := by sorry
