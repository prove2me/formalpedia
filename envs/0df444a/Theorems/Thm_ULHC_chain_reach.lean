-- Prove2me | Theorems.Thm_ULHC_chain_reach
-- name    : ULHC.chain_reach
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:56:42.539845+00:00
-- url     : https://prove2.me/theorems/26e96240-ce3d-4124-aac6-6da9e8000cec
-- title:
--   ULHC: chain reach
-- statement:
--   The ULHC construction uses the chain reach property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Planar.lean#L119-L128
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Planar.lean#L119-L128

import Definitions.Def_ULHC_Conn
import Definitions.Def_ULHC_Planar
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.chain_reach {r : Pt → Pt → Prop} {u : Pt} {l : List Pt} (h : List.IsChain r (u :: l))
    {z : Pt} (hz : z ∈ u :: l) : Relation.ReflTransGen r u z := by sorry
