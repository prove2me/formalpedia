-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_deferredAcceptanceMatching_eq_unique
-- name    : TunnellMap.GloballyRanked.DAState.deferredAcceptanceMatching_eq_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:34:48.501434+00:00
-- url     : https://prove2.me/theorems/e7c13e20-4786-5947-95db-6b1bd9825eb8
-- title:
--   DAState: deferred Acceptance Matching eq unique
-- statement:
--   The executable FIFO algorithm returns the unique stable matching already
--   characterized abstractly.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceStability.lean#L317-L325
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceStability.lean#L317-L325

import Definitions.Def_TunnellMap_DeferredAcceptanceOutput
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Theorems.Thm_TunnellMap_GloballyRanked_exists_unique_stable

set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)

theorem TunnellMap.GloballyRanked.DAState.deferredAcceptanceMatching_eq_unique
    (hcard : Fintype.card S = Fintype.card T)
    (sourceOrder : List S) (hnodup : sourceOrder.Nodup)
    (hcomplete : ∀ s, s ∈ sourceOrder) :
    deferredAcceptanceMatching I hcard sourceOrder hnodup hcomplete =
      Classical.choose (I.exists_unique_stable hcard) := by sorry
