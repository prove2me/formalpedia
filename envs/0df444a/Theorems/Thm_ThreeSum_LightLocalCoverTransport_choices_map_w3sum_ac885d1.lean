-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverTransport_choices_map_w3sum_ac885d1
-- name    : ThreeSum.LightLocalCoverTransport.choices_map_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:24:23.399243+00:00
-- url     : https://prove2.me/theorems/d430c824-de07-44ad-bad4-c87da8a9f74c
-- title:
--   Light Local Cover Transport: choices map
-- statement:
--   The Light Local Cover Transport construction uses the choices map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverTransport.lean#L17-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverTransport.lean#L17-L77

import Definitions.Def_Submission_ThreeSum_BooleanGreedy
import Definitions.Def_Submission_ThreeSum_LightLocalCoverTransport
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverTransport
open Finset
variable {Ω U : Type*} [Inhabited Ω] [DecidableEq U]

theorem ThreeSum.LightLocalCoverTransport.choices_map_w3sum_ac885d1
    (matrix : ℕ → ℕ → ℕ) (candidate : ℕ → Ω) (target : ℕ → U)
    (covers : Ω → U → Prop) [DecidableRel covers]
    {rows cols : ℕ} (hrows : 0 < rows)
    (hinj : Set.InjOn target (range cols))
    (hcover : ∀ i, ∀ j < cols, BooleanGreedy.covers matrix i j ↔ covers (candidate i) (target j))
    (rounds : ℕ) :
    (BooleanGreedy.choices matrix rows cols rounds).map candidate =
      Cover.greedyChoices ((List.range rows).map candidate) covers
        ((range cols).image target) rounds := by sorry
