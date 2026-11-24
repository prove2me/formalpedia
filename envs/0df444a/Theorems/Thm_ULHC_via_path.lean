-- Prove2me | Theorems.Thm_ULHC_via_path
-- name    : ULHC.via_path
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:30:12.265471+00:00
-- url     : https://prove2.me/theorems/6b8a4951-083d-41ec-94ed-9a8474fc4c2b
-- title:
--   ULHC: via path
-- statement:
--   The ULHC construction uses the via path property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/PathComplete.lean#L58-L77
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/PathComplete.lean#L58-L77

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
include hs x0 hconn hG hT ha hae ha2 hT'
omit hs x0 hconn

theorem ULHC.via_path : ∀ (n : ℕ) (w : StripSpec) (R : List StripSpec), CRPathCA V G a (w :: R) →
    wt a (w :: R) = n → (∀ x ∈ R, ¬ Touches a x) →
    (R ≠ [] → ∀ j < a.n, ∀ y ∈ cellE (endCell w), y ∉ cellE (cellJ a.c a.s j)) →
    ∃ σ L, CRPathCA V (applyS G a) σ L := by sorry
