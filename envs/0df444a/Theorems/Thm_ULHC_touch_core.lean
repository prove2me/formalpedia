-- Prove2me | Theorems.Thm_ULHC_touch_core
-- name    : ULHC.touch_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:05:01.931258+00:00
-- url     : https://prove2.me/theorems/c506bae1-f22d-4480-a8c4-9be6d4e78992
-- title:
--   ULHC: touch core
-- statement:
--   The ULHC construction uses the touch core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L1120-L1379
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L1120-L1379

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
omit hs x0 hconn

theorem ULHC.touch_core {σ τ : StripSpec} {i0 : ℕ} {L2 : List StripSpec} (hl : CR2 V G σ τ)
    (hzs : SigFrom G τ.c τ.s τ.n i0) (hi01 : i0 ≤ 1) (hz0 : i0 = 0 → NoChain σ τ)
    (hne_e : i0 = 1 → τ.c ≠ endCell a)
    (hσ : EndOK V G σ) (hσe : σ.n % 2 = 0) (hch : CRChain V G τ L2)
    (hnct : CATail (τ :: L2)) (hfar2 : ∀ w ∈ L2, ¬ Touches a w)
    {W2 : ℕ} (hvia : ViaFree V G a W2) (hW1 : wt τ L2 < W) (hW2 : a.n + wt τ L2 < W2) {i j : ℕ} (hii : i0 ≤ i) (hi : i < τ.n) (hj : j < a.n)
    {x : Edge} (hx1 : x ∈ cellE (cellJ τ.c τ.s i)) (hx2 : x ∈ cellE (cellJ a.c a.s j)) :
    False := by sorry
