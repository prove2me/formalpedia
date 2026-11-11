-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_rx_region_card
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.rx_region_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:06:39.972194+00:00
-- url     : https://prove2.me/theorems/cd783ac4-cdd3-4f93-91e5-4594299066a2
-- title:
--   BDL26 Paired History Query Cone: rx region card
-- statement:
--   The full actual syndrome fibre, identified with its raw constructor chart.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/ReadBounds.lean#L61-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/ReadBounds.lean#L61-L80

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_LocalReads
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_ReadBounds
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedHistoryQueryCone
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26RXCoarseInfluence
open BDL26RXInfluenceBounds BDL26GraphQuantitativeBounds
open MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26PairedHistoryQueryCone.rx_region_card (h : i.val % 2 = 0) (v : Owners S depth i) :
    ((rxXiLocalComplex (rxData S depth i h)).syndromeRegion v).card ≤
      localCoordinateBound S := by sorry
