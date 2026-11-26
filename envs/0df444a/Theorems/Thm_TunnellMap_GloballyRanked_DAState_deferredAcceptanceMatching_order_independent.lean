-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_deferredAcceptanceMatching_order_independent
-- name    : TunnellMap.GloballyRanked.DAState.deferredAcceptanceMatching_order_independent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:35:59.229799+00:00
-- url     : https://prove2.me/theorems/d1978fb3-3c0f-57f1-914d-591cdbea4b34
-- title:
--   DAState: deferred Acceptance Matching order independent
-- statement:
--   Changing the deterministic initial queue order cannot change the output in
--   a globally ranked instance, because the stable perfect matching is unique.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceStability.lean#L329-L337
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceStability.lean#L329-L337

import Definitions.Def_TunnellMap_DeferredAcceptanceOutput
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)

theorem TunnellMap.GloballyRanked.DAState.deferredAcceptanceMatching_order_independent
    (hcard : Fintype.card S = Fintype.card T)
    (order₁ order₂ : List S)
    (hnodup₁ : order₁.Nodup) (hnodup₂ : order₂.Nodup)
    (hcomplete₁ : ∀ s, s ∈ order₁) (hcomplete₂ : ∀ s, s ∈ order₂) :
    deferredAcceptanceMatching I hcard order₁ hnodup₁ hcomplete₁ =
      deferredAcceptanceMatching I hcard order₂ hnodup₂ hcomplete₂ := by sorry
