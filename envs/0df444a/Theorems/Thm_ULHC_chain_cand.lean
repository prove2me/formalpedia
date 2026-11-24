-- Prove2me | Theorems.Thm_ULHC_chain_cand
-- name    : ULHC.chain_cand
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:58:52.379458+00:00
-- url     : https://prove2.me/theorems/e6207eed-0c80-4b2a-8c1c-8c1e42f7df35
-- title:
--   ULHC: chain cand
-- statement:
--   The ULHC construction uses the chain cand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/LinkGraph.lean#L186-L194
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/LinkGraph.lean#L186-L194

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_LinkGraph
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}

theorem ULHC.chain_cand : ∀ (L : List StripSpec) (b : StripSpec), 1 ≤ b.n →
    (∀ j < b.n, IsCell V (cellJ b.c b.s j)) → CRChain V G b L → ∀ c ∈ L, c ∈ cand V G
  := by sorry
