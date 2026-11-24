-- Prove2me | Theorems.Thm_ULHC_src_notouch
-- name    : ULHC.src_notouch
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:39:25.211749+00:00
-- url     : https://prove2.me/theorems/dc7798f9-0839-4d59-87cf-b7755a909464
-- title:
--   ULHC: src notouch
-- statement:
--   The ULHC construction uses the src notouch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/PathComplete.lean#L113-L117
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/PathComplete.lean#L113-L117

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

theorem ULHC.src_notouch {q : StripSpec} {L : List StripSpec} (hP : CRPathCA V G q L)
    (hWq : W = wt q L) (hno : ¬ ∃ σ L', CRPathCA V (applyS G a) σ L') : ∀ τ ∈ L, ¬ Touches a τ := by sorry
