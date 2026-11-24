-- Prove2me | Theorems.Thm_ULHC_touch_contra_chain
-- name    : ULHC.touch_contra_chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:05:02.381057+00:00
-- url     : https://prove2.me/theorems/1eec7c68-884b-4cb4-9425-104a38186f07
-- title:
--   ULHC: touch contra chain
-- statement:
--   The ULHC construction uses the touch contra chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L1387-L1551
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L1387-L1551

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

theorem ULHC.touch_contra_chain {σ τ : StripSpec} {L2 : List StripSpec} (hl : CR2 V G σ τ)
    (hok : ChainOK σ τ) (hch' : ¬ NoChain σ τ) (hσ : EndOK V G σ) (hσe : σ.n % 2 = 0)
    (hch : CRChain V G τ L2) (hnct : CATail (τ :: L2)) (hfar2 : ∀ w ∈ L2, ¬ Touches a w)
    {W2 : ℕ} (hvia : ViaFree V G a W2) (hW1 : wt τ L2 < W) (hW2 : a.n + wt τ L2 < W2) :
    ¬ Touches a τ := by sorry
