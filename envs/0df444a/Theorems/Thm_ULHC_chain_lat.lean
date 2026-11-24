-- Prove2me | Theorems.Thm_ULHC_chain_lat
-- name    : ULHC.chain_lat
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:28:54.773794+00:00
-- url     : https://prove2.me/theorems/73a39308-c765-4e9f-8399-9a78d601baad
-- title:
--   ULHC: chain lat
-- statement:
--   The ULHC construction uses the chain lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/ChainLinks.lean#L89-L120
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/ChainLinks.lean#L89-L120

import Definitions.Def_ULHC_NearLemma
import Definitions.Def_ULHC_ChainLinks
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}

theorem ULHC.chain_lat {b c : StripSpec} (hl : CR2 V G b c) (hok : ChainOK b c)
    (hlu : lat1 (endCell b) b.s ∈ G ∧ lat2 (endCell b) b.s ∈ G) {x : Edge}
    (hx : x ∈ cellE c.c) (hxu : x ∈ cellE (endCell b)) :
    x = lat1 c.c c.s ∨ x = lat2 c.c c.s := by sorry
