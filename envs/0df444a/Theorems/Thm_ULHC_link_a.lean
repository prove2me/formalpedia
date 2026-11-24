-- Prove2me | Theorems.Thm_ULHC_link_a
-- name    : ULHC.link_a
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:21:35.635536+00:00
-- url     : https://prove2.me/theorems/d26e79b3-9d89-4d39-9385-21c9083957ea
-- title:
--   ULHC: link a
-- statement:
--   The ULHC construction uses the link a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearLemma.lean#L61-L87
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearLemma.lean#L61-L87

import Definitions.Def_ULHC_NearChain
import Definitions.Def_ULHC_NearLemma
import Theorems.Thm_ULHC_APair_flip

set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge} {a : StripSpec}
  (hG : Deg2 V G) (ha : ValidStrip V G a) (hae : a.n % 2 = 0) (ha2 : 2 ≤ a.n)
include hG ha hae ha2

theorem ULHC.link_a {w : StripSpec} (hw1 : 1 ≤ w.n) (hpw : StripPat G w.c w.s w.n)
    (hcw : ∀ j < w.n, IsCell V (cellJ w.c w.s j)) (hnt : ¬ Touches a w)
    (hcg : Conn G (back1 w.c w.s) (front1 w.c w.s))
    (hcu : ¬ Conn (flip G (endCell a)) (back1 w.c w.s) (front1 w.c w.s)) : CR2 V G a w := by sorry
