-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXStagedRestriction_seedError_q_syndrome_one
-- name    : QEC.Coding.BDL26RXStagedRestriction.seedError_q_syndrome_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:43:04.902254+00:00
-- url     : https://prove2.me/theorems/1ed5785a-f819-4544-a53c-341f44533026
-- title:
--   BDL26 RXStaged Restriction: seed Error q syndrome one
-- statement:
--   The BDL26 RXStaged Restriction construction uses the seed Error q syndrome one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXStagedRestriction.lean#L93-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXStagedRestriction.lean#L93-L96

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXStagedRestriction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXStagedRestriction
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26ReplacementSupport BDL26ReplacementCochainMaps
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXStagedRestriction.seedError_q_syndrome_one :
    rxCoboundary1 baseTannerSquarePresentation scaleFive seedError
      (Sum.inl (Sum.inr ⟨(0 : BaseQubit),seedQEdge⟩)) = 1 := by sorry
