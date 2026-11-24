-- Prove2me | Theorems.Thm_ULHC_near_far_CA
-- name    : ULHC.near_far_CA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:05:14.462044+00:00
-- url     : https://prove2.me/theorems/28938aeb-6000-44d0-b6f7-4f4c6d9fbac3
-- title:
--   ULHC: near far CA
-- statement:
--   The ULHC construction uses the near far CA property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L1646-L1664
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L1646-L1664

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

theorem ULHC.near_far_CA {b : StripSpec} {L : List StripSpec} (hP : CRPathCA V G a (b :: L))
    (hWeq : W = wt a (b :: L)) : FarChainCA G a b L := by sorry
