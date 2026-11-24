-- Prove2me | Theorems.Thm_ULHC_comp_clean
-- name    : ULHC.comp_clean
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:08:20.141634+00:00
-- url     : https://prove2.me/theorems/afacdde6-2e90-4fea-ae54-67b155f7a563
-- title:
--   ULHC: comp clean
-- statement:
--   The ULHC construction uses the comp clean property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/PathComplete.lean#L391-L587
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/PathComplete.lean#L391-L587

import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_AlgComplete
import Definitions.Def_ULHC_PathComplete
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge} {c : Pt} {d : Side} {k : ℕ}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hG : Deg2 V G) (hT : NoTypeIII V G) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c d j)) (hpat : StripPat G c d (k + 2))
  (hsep : ¬ Conn G (back1 c d) (front1 c d)) (hT' : NoTypeIII V (flipCol G c d (k + 2)))
include hs x0 hconn hG hT hk hcell hpat hsep hT'

theorem ULHC.comp_clean {q : StripSpec} {L : List StripSpec}
    (hP : CRPathCA V (flipCol G c d (k + 2)) q L)
    (hmin : ∀ σ L', CRPathCA V (flipCol G c d (k + 2)) σ L' → wt q L ≤ wt σ L') :
    ∃ σ L', CRPathCA V G σ L' := by sorry
