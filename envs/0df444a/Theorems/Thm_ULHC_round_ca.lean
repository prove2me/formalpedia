-- Prove2me | Theorems.Thm_ULHC_round_ca
-- name    : ULHC.round_ca
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:05:10.512826+00:00
-- url     : https://prove2.me/theorems/09d7d008-1e6e-4eb5-b021-0041b7927acd
-- title:
--   ULHC: round ca
-- statement:
--   The ULHC construction uses the round ca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L1669-L1673
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L1669-L1673

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge} {a : StripSpec}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hG : Deg2 V G) (hT : NoTypeIII V G) (ha : ValidStrip V G a) (hae : a.n % 2 = 0)
  (ha2 : 2 ≤ a.n) (hT' : NoTypeIII V (applyS G a))
  {W : ℕ} (hmin : ∀ σ L', CRPathCA V G σ L' → W ≤ wt σ L')
include hs x0 hconn hG hT ha hae ha2 hT' hmin

theorem ULHC.round_ca {b : StripSpec} {L : List StripSpec} (hP : CRPathCA V G a (b :: L))
    (hWeq : W = wt a (b :: L)) :
    CRPathCA V (applyS G a) b L ∧ wt b L + a.n = wt a (b :: L) := by sorry
