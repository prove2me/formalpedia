-- Prove2me | Theorems.Thm_ULHC_even_light_inter
-- name    : ULHC.even_light_inter
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:50:32.835447+00:00
-- url     : https://prove2.me/theorems/c3ec8dd9-2928-4f5d-a889-1755a38eab90
-- title:
--   ULHC: even light inter
-- statement:
--   The ULHC construction uses the even light inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Created.lean#L37-L41
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Created.lean#L37-L41

import Definitions.Def_ULHC_Reroute
import Definitions.Def_ULHC_Created
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.even_light_inter {V : Finset Pt} {F : Finset Edge} (hs : Solid V) (hFV : Inside V F)
    (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z) {B : Finset Edge}
    (heven : ∀ c, IsCell V c → sidesIn B c % 2 = 0) (hl : ∀ f ∈ B, f ∉ F) {e : Edge}
    (hE : IsEdge V e) (he : e ∈ B) : ¬ Conn F e.p e.q := by sorry
