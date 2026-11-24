-- Prove2me | Theorems.Thm_ULHC_inter_unique
-- name    : ULHC.inter_unique
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:28:47.031811+00:00
-- url     : https://prove2.me/theorems/dc480aed-fa4b-4a2f-889b-4baaa3522a10
-- title:
--   ULHC: inter unique
-- statement:
--   The ULHC construction uses the inter unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/ChainLinks.lean#L68-L81
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/ChainLinks.lean#L68-L81

import Definitions.Def_ULHC_NearLemma
import Definitions.Def_ULHC_ChainLinks
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.inter_unique {d u : Pt} (hne : d ≠ u) {x y : Edge} (hx : x ∈ cellE d) (hxu : x ∈ cellE u)
    (hy : y ∈ cellE d) (hyu : y ∈ cellE u) : x = y := by sorry
