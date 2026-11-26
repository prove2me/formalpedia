-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_mem_take_of_rank_lt_of_mem_take
-- name    : TunnellMap.GloballyRanked.DAState.mem_take_of_rank_lt_of_mem_take
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:35:00.504475+00:00
-- url     : https://prove2.me/theorems/546c2410-3731-4fc3-aa8d-ce6949635f69
-- title:
--   DAState: mem take of rank lt of mem take
-- statement:
--   In a source's sorted preference list, every target with smaller key than
--   an already tried target has also been tried.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceStability.lean#L239-L263
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceStability.lean#L239-L263

import Definitions.Def_TunnellMap_DeferredAcceptanceOutput
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)

theorem TunnellMap.GloballyRanked.DAState.mem_take_of_rank_lt_of_mem_take (s : S) {t u : T} {k : ℕ}
    (hrank : I.rank s t < I.rank s u)
    (hu : u ∈ (I.preferenceList s).take k) :
    t ∈ (I.preferenceList s).take k := by sorry
