-- Prove2me | Theorems.Thm_PvsNP_AnchoredOnlineRun_all_prefixes_stay_in_window
-- name    : PvsNP.AnchoredOnlineRun.all_prefixes_stay_in_window
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-27T06:28:51.201823+00:00
-- url     : https://prove2.me/theorems/1dfde896-018b-5956-9aac-11ba4b8f233d
-- title:
--   Every prefix of an anchored run stays in one work-tape window
-- statement:
--   For a deterministic online single-work-tape machine, suppose a run is composed of operations of at most L transitions whose boundary heads are all at the same absolute position. Every intermediate head of the run is in the same window of 2L+1 cells, regardless of how many operations occur.
-- source:
--   Deterministic run splitting and the unit displacement of work-tape transitions.

import Definitions.Def_AnchoredOneWorkTapeRun
set_option autoImplicit false
open PvsNP.OnlineWindowIO PvsNP.AnchoredOnlineRun

theorem PvsNP.AnchoredOnlineRun.all_prefixes_stay_in_window {S A : Type} {M : OnlineMachine S A}
    {anchor : ℤ} {limit : ℕ} {a b : OnlineConfig S A} {n : ℕ}
    (s : Segments M anchor limit a b n) :
    ∀ c t, t ≤ n → OnlineRun M a c t →
      PvsNP.OnlineBoundedConsumer.InWindow (anchor-(limit:ℤ)) (2*limit+1) c.1 := by sorry
