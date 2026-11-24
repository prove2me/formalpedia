-- Prove2me | Theorems.Thm_ULHC_tail_of_chain
-- name    : ULHC.tail_of_chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:59:19.148372+00:00
-- url     : https://prove2.me/theorems/4165b339-9f9b-4394-a316-b2c2e762cb7f
-- title:
--   ULHC: tail of chain
-- statement:
--   The ULHC construction uses the tail of chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/LinkGraph.lean#L200-L221
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/LinkGraph.lean#L200-L221

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_LinkGraph
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}

theorem ULHC.tail_of_chain (hGV : Inside V G) : ∀ (L : List StripSpec) (b : StripSpec) (k : ℕ),
    1 ≤ b.n → (∀ j < b.n, IsCell V (cellJ b.c b.s j)) → CRChain V G b L → CATail (b :: L) →
    MP.IsTail gmid gtgt (gedge V G) ⟨b, k⟩ (posList (min (k + 1) 3) L) := by sorry
