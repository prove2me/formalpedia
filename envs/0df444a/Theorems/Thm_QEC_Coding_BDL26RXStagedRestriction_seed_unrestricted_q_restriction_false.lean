-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXStagedRestriction_seed_unrestricted_q_restriction_false
-- name    : QEC.Coding.BDL26RXStagedRestriction.seed_unrestricted_q_restriction_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:13:24.625691+00:00
-- url     : https://prove2.me/theorems/df8a3091-71ec-4647-8ee1-405db3382d4f
-- title:
--   BDL26 RXStaged Restriction: seed unrestricted q restriction false
-- statement:
--   The previous unconditional restriction cannot hold for the actual fibres.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXStagedRestriction.lean#L99-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXStagedRestriction.lean#L99-L109

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXStagedRestriction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXStagedRestriction
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26ReplacementSupport BDL26ReplacementCochainMaps
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXStagedRestriction.seed_unrestricted_q_restriction_false :
    ¬ (∀ e : Word BDL26Field (RX1 baseTannerSquarePresentation scaleFive),
      rxCoboundary1 baseTannerSquarePresentation scaleFive e
        (Sum.inl (Sum.inr ⟨(0 : BaseQubit),seedQEdge⟩)) =
      wordLinearMapTranspose (qDoubleCylinderBoundary1 baseTannerSquarePresentation
        (0 : BaseQubit) scaleFive)
        (fun vertex => e (Sum.inr ⟨(0 : BaseQubit),vertex⟩)) seedQEdge) := by sorry
