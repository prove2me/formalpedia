-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_rx_coarse_agreement
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.rx_coarse_agreement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:00:17.426536+00:00
-- url     : https://prove2.me/theorems/fb9c78a5-4305-4d1b-85e6-b3a46b5431d9
-- title:
--   BDL26 History Syndrome Sensitivity: rx coarse agreement
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the rx coarse agreement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Steps.lean#L40-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Steps.lean#L40-L64

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXInfluenceBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Steps
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26RXDecoderAdapter BDL26RZDecoderAdapter
open BDL26RXCoarseInfluence BDL26RXInfluenceBounds MultiscaleDecoder
open RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.rx_coarse_agreement (h : i.val % 2 = 0)
    (sigma tau : (indexedFamily S depth).Syndrome i.succ)
    (z : FamilyZ S depth i.castSucc)
    (ha : ∀ p ∈ readRegion S depth i h z, sigma.val p = tau.val p) :
    (rxStepOutput S depth i h sigma).coarse.val z =
      (rxStepOutput S depth i h tau).coarse.val z := by sorry
