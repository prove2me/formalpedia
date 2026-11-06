-- Prove2me | Theorems.Thm_QEC_Locality_measuredTwoThirdsLeft_subset
-- name    : QEC.Locality.measuredTwoThirdsLeft_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:04:51.363287+00:00
-- url     : https://prove2.me/theorems/4d808b22-8fce-4f3a-b2ea-80256849210f
-- title:
--   Locality: measured Two Thirds Left subset
-- statement:
--   The Locality construction uses the measured Two Thirds Left subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/RecursiveSeparator.lean#L62-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/RecursiveSeparator.lean#L62-L70

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.measuredTwoThirdsLeft_subset
    (G : ConnectivityGraph ι) (vertices : Finset ι) :
    measuredTwoThirdsLeft G vertices ⊆ vertices := by sorry
