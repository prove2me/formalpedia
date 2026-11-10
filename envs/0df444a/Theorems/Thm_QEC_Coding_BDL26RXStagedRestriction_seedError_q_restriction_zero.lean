-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXStagedRestriction_seedError_q_restriction_zero
-- name    : QEC.Coding.BDL26RXStagedRestriction.seedError_q_restriction_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:42:48.142336+00:00
-- url     : https://prove2.me/theorems/0409a312-6b2a-4bb4-a35f-92cb508277d5
-- title:
--   BDL26 RXStaged Restriction: seed Error q restriction zero
-- statement:
--   The BDL26 RXStaged Restriction construction uses the seed Error q restriction zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXStagedRestriction.lean#L88-L91
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXStagedRestriction.lean#L88-L91

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXStagedRestriction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXStagedRestriction
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26ReplacementSupport BDL26ReplacementCochainMaps
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXStagedRestriction.seedError_q_restriction_zero (q : BaseQubit) :
    (fun vertex : QDoubleCylinderVertex baseTannerSquarePresentation q scaleFive =>
      seedError (Sum.inr ⟨q,vertex⟩)) = 0 := by sorry
