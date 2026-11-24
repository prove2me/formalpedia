-- Prove2me | Theorems.Thm_ULHC_closed_chain_even
-- name    : ULHC.closed_chain_even
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:52:52.990094+00:00
-- url     : https://prove2.me/theorems/b1fe5238-3e7a-4cab-a987-060761e2665c
-- title:
--   ULHC: closed chain even
-- statement:
--   The ULHC construction uses the closed chain even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L460-L505
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L460-L505

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v


set_option autoImplicit true
open ULHC
open Finset Classical
variable {G : Finset Edge}

theorem ULHC.closed_chain_even {V : Finset Pt} (hs : Solid V) (hG : ∀ e ∈ G, e.p ∈ V ∧ e.q ∈ V)
    (B : Finset Edge) (heven : ∀ c, IsCell V c → sidesIn B c % 2 = 0)
    {u : Pt} {l : List Pt} (hc : List.IsChain (Adj G) (u :: l))
    (hl : (u :: l).getLast (by simp) = u) : crossL B u l % 2 = 0 := by sorry
