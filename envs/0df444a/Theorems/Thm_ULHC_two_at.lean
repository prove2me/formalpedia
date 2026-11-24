-- Prove2me | Theorems.Thm_ULHC_two_at
-- name    : ULHC.two_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:27:41.750833+00:00
-- url     : https://prove2.me/theorems/ac78b630-2e7c-4eff-b189-c2daf656a3ab
-- title:
--   ULHC: two at
-- statement:
--   The ULHC construction uses the two at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearLemma.lean#L164-L170
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearLemma.lean#L164-L170

import Definitions.Def_ULHC_NearChain
import Definitions.Def_ULHC_NearLemma
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.two_at {A : Finset Edge} {p : Pt} {g1 g2 x : Edge} (hdeg : deg A p = 2) (h1 : g1 ∈ A)
    (h2 : g2 ∈ A) (i1 : g1.p = p ∨ g1.q = p) (i2 : g2.p = p ∨ g2.q = p) (n12 : g1 ≠ g2)
    (hx : x ∈ A) (ix : x.p = p ∨ x.q = p) : x = g1 ∨ x = g2 := by sorry
