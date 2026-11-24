-- Prove2me | Theorems.Thm_ULHC_Ends_adj_cases
-- name    : ULHC.Ends.adj_cases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:54:41.149912+00:00
-- url     : https://prove2.me/theorems/7f0345ff-4a42-4a62-a834-409e4ece734e
-- title:
--   Ends: adj cases
-- statement:
--   The Ends construction uses the adj cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Stacked.lean#L45-L52
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Stacked.lean#L45-L52

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Stacked
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.Ends.adj_cases {g : Edge} {s tf u v : Pt} (h : Ends g s tf)
    (huv : (g.p = u ∧ g.q = v) ∨ (g.p = v ∧ g.q = u)) :
    (u = s ∧ v = tf) ∨ (u = tf ∧ v = s) := by sorry
