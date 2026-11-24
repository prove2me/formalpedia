-- Prove2me | Theorems.Thm_ULHC_chain_of_tail
-- name    : ULHC.chain_of_tail
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:59:25.512443+00:00
-- url     : https://prove2.me/theorems/229318b2-0bd3-4ca2-996a-ecd4b4e31f29
-- title:
--   ULHC: chain of tail
-- statement:
--   The ULHC construction uses the chain of tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/LinkGraph.lean#L252-L280
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/LinkGraph.lean#L252-L280

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_LinkGraph
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}

theorem ULHC.chain_of_tail (hGV : Inside V G) : ∀ (rest : List Node) (x : Node),
    MP.IsTail gmid gtgt (gedge V G) x rest → (∀ y ∈ x :: rest, y ∈ candN V G) →
    ∃ L, rest = posList (min (x.pos + 1) 3) L ∧ CRChain V G x.σ L ∧ CATail (x.σ :: L) := by sorry
