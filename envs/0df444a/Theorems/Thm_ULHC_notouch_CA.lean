-- Prove2me | Theorems.Thm_ULHC_notouch_CA
-- name    : ULHC.notouch_CA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:38:23.198811+00:00
-- url     : https://prove2.me/theorems/b261f48f-f840-47f5-8b87-3d9e1ff02b13
-- title:
--   ULHC: notouch CA
-- statement:
--   The ULHC construction uses the notouch CA property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L1553-L1573
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L1553-L1573

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

theorem ULHC.notouch_CA {W2 : ℕ} (hvia : ViaFree V G a W2) : ∀ (L : List StripSpec) (σ : StripSpec),
    CRChain V G σ L → CATail (σ :: L) → EndOK V G σ → wt σ L ≤ W → a.n + wt σ L ≤ W2 →
    ∀ τ ∈ L, ¬ Touches a τ := by sorry
