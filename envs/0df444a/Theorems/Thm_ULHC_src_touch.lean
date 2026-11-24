-- Prove2me | Theorems.Thm_ULHC_src_touch
-- name    : ULHC.src_touch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:07:24.576558+00:00
-- url     : https://prove2.me/theorems/be346fb7-50a8-42c9-b1ac-ef311db3e7d2
-- title:
--   ULHC: src touch
-- statement:
--   The ULHC construction uses the src touch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/PathComplete.lean#L122-L302
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/PathComplete.lean#L122-L302

import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_AlgComplete
import Definitions.Def_ULHC_PathComplete
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge} {a : StripSpec}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hG : Deg2 V G) (hT : NoTypeIII V G) (ha : ValidStrip V G a) (hae : a.n % 2 = 0)
  (ha2 : 2 ≤ a.n) (hT' : NoTypeIII V (applyS G a))
  {W : ℕ} (hmin : ∀ σ L', CRPathCA V G σ L' → W ≤ wt σ L')
include hs x0 hconn hG hT ha hae ha2 hT' hmin

theorem ULHC.src_touch {q : StripSpec} {L : List StripSpec} (hP : CRPathCA V G q L)
    (hWq : W = wt q L) (hno : ¬ ∃ σ L', CRPathCA V (applyS G a) σ L') (htq : Touches a q) :
    q.s = a.s.opp ∧ (q.c = nb a.c (latA a.s) ∨ q.c = nb a.c (latB a.s)) := by sorry
