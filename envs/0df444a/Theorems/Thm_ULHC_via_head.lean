-- Prove2me | Theorems.Thm_ULHC_via_head
-- name    : ULHC.via_head
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:07:10.746285+00:00
-- url     : https://prove2.me/theorems/f9ac351e-c424-4128-aa40-c36e85861ac3
-- title:
--   ULHC: via head
-- statement:
--   The ULHC construction uses the via head property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/PathComplete.lean#L83-L98
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/PathComplete.lean#L83-L98

import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_AlgComplete
import Definitions.Def_ULHC_PathComplete
import Theorems.Thm_ULHC_APair_flip

set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge} {a : StripSpec}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hG : Deg2 V G) (hT : NoTypeIII V G) (ha : ValidStrip V G a) (hae : a.n % 2 = 0)
  (ha2 : 2 ≤ a.n) (hT' : NoTypeIII V (applyS G a))
include hs x0 hconn hG hT ha hae ha2 hT'
omit hs x0 hconn

theorem ULHC.via_head {q w : StripSpec} {L3 : List StripSpec} (hch : CRChain V G q (w :: L3))
    (hcat : CATail (q :: w :: L3)) (hntL : ∀ τ ∈ w :: L3, ¬ Touches a τ)
    (hpw : StripPat G w.c w.s w.n)
    (hsplit : ¬ Conn (flip G (endCell a)) (back1 w.c w.s) (front1 w.c w.s)) :
    ∃ σ L, CRPathCA V (applyS G a) σ L := by sorry
