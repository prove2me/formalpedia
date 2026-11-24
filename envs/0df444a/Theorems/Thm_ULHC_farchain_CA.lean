-- Prove2me | Theorems.Thm_ULHC_farchain_CA
-- name    : ULHC.farchain_CA
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:30:32.353675+00:00
-- url     : https://prove2.me/theorems/5dd46da5-4164-4ec9-91b1-e14954de3b61
-- title:
--   ULHC: farchain CA
-- statement:
--   The ULHC construction uses the farchain CA property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L1576-L1641
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L1576-L1641

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
omit hs x0 hconn hT hT' hmin

theorem ULHC.farchain_CA {W2 : ℕ} (hvia : ViaFree V G a W2) : ∀ (L : List StripSpec) (σ : StripSpec),
    CRChain V G σ L → CATail (σ :: L) → EndOK V G σ →
    (∀ j < a.n, ∀ y ∈ cellE (endCell σ), y ∉ cellE (cellJ a.c a.s j)) →
    (∀ τ ∈ L, ¬ Touches a τ) → a.n + wt σ L ≤ W2 → FarChainCA G a σ L := by sorry
