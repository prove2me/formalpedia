-- Prove2me | Theorems.Thm_QEC_Locality_measuredTwoThirdsRight_subset
-- name    : QEC.Locality.measuredTwoThirdsRight_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:05:23.021201+00:00
-- url     : https://prove2.me/theorems/ee399d8f-8f0a-4af2-ae30-3d1a638a5ae2
-- title:
--   Locality: measured Two Thirds Right subset
-- statement:
--   The Locality construction uses the measured Two Thirds Right subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/RecursiveSeparator.lean#L72-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/RecursiveSeparator.lean#L72-L80

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

theorem QEC.Locality.measuredTwoThirdsRight_subset
    (G : ConnectivityGraph ι) (vertices : Finset ι) :
    measuredTwoThirdsRight G vertices ⊆ vertices := by sorry
