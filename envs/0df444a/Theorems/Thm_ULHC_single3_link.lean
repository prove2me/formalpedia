-- Prove2me | Theorems.Thm_ULHC_single3_link
-- name    : ULHC.single3_link
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:04:12.225005+00:00
-- url     : https://prove2.me/theorems/f9b060c3-18e7-422c-8172-073122ad65ca
-- title:
--   ULHC: single3 link
-- statement:
--   The ULHC construction uses the single3 link property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L729-L808
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L729-L808

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.single3_link {V : Finset Pt} {G : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
    (hG : Deg2 V G) (hT : NoTypeIII V G) (hk : k % 2 = 0)
    (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat G c s (k + 2))
    (hd1 : lat1 (cellJ c s (k + 2)) s ∈ G) (hd2 : lat2 (cellJ c s (k + 2)) s ∈ G)
    (hdf : front (cellJ c s (k + 2)) s ∈ G) (hcu : IsCell V (cellJ c s (k + 3)))
    {tu : Side} (lu1 : lat1 (cellJ c s (k + 3)) tu ∈ G) (lu2 : lat2 (cellJ c s (k + 3)) tu ∈ G)
    (bu : back (cellJ c s (k + 3)) tu ∉ G) (fu : front (cellJ c s (k + 3)) tu ∉ G)
    (hcd : IsCell V (cellJ c s (k + 2))) :
    CR2 V G ⟨c, s, k + 2⟩ ⟨cellJ c s (k + 3), s, 1⟩ := by sorry
