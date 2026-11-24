-- Prove2me | Theorems.Thm_ULHC_e1_chain
-- name    : ULHC.e1_chain
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:29:27.399152+00:00
-- url     : https://prove2.me/theorems/2727bdae-87e9-4899-bee9-8500908711a2
-- title:
--   ULHC: e1 chain
-- statement:
--   The ULHC construction uses the e1 chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L29-L150
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L29-L150

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hG : Deg2 V G) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat G c s (k + 2))
include hG hk hcell hpat

theorem ULHC.e1_chain {τ w : StripSpec} (hl : CR2 V G τ w) (hok : ChainOK τ w)
    (hend : endCell τ = nb (cellJ c s (k + 1)) s) (ht : τ.s = s.opp)
    (hul1 : lat1 (nb (cellJ c s (k + 1)) s) s ∈ G) (hul2 : lat2 (nb (cellJ c s (k + 1)) s) s ∈ G)
    {y : Edge} (hy : y ∈ cellE (cellJ w.c w.s 0)) (hyu : y ∈ cellE (nb (cellJ c s (k + 1)) s))
    (hyl : y = lat1 (nb (cellJ c s (k + 1)) s) τ.s ∨ y = lat2 (nb (cellJ c s (k + 1)) s) τ.s) :
    Touches ⟨c, s, k + 2⟩ w := by sorry
