-- Prove2me | Theorems.Thm_ULHC_mem_candN
-- name    : ULHC.mem_candN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:22:14.505616+00:00
-- url     : https://prove2.me/theorems/f1c0d59b-4ab5-4904-9db3-b8b9cecf987a
-- title:
--   ULHC: mem cand N
-- statement:
--   The ULHC construction uses the mem cand N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/LinkGraph.lean#L139-L148
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/LinkGraph.lean#L139-L148

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_LinkGraph
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}

theorem ULHC.mem_candN {x : Node} :
    x ∈ candN V G ↔ x.σ ∈ cand V G ∧ x.pos ∈ ({1, 2, 3} : Finset ℕ) := by sorry
