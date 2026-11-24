-- Prove2me | Theorems.Thm_ULHC_chain_start
-- name    : ULHC.chain_start
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:36:16.250843+00:00
-- url     : https://prove2.me/theorems/eb1f09df-eb48-463c-b7de-b779b073c68b
-- title:
--   ULHC: chain start
-- statement:
--   The ULHC construction uses the chain start property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/ChainLinks.lean#L145-L183
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/ChainLinks.lean#L145-L183

import Definitions.Def_ULHC_NearLemma
import Definitions.Def_ULHC_ChainLinks
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}

theorem ULHC.chain_start {b c : StripSpec} (hl : CR2 V G b c) (hok : ChainOK b c)
    (hlu : lat1 (endCell b) b.s ∈ G ∧ lat2 (endCell b) b.s ∈ G) {x : Edge}
    (hx : x ∈ cellE c.c) (hxu : x ∈ cellE (endCell b)) :
    x ∈ G ∧ (x = lat1 c.c c.s ∨ x = lat2 c.c c.s) ∧ back c.c c.s ∈ G ∧
      (front c.c c.s ∈ G ↔ c.n = 1) ∧
      ((lat1 c.c c.s ∈ G ∧ lat2 c.c c.s ∉ G) ∨ (lat2 c.c c.s ∈ G ∧ lat1 c.c c.s ∉ G)) := by sorry
