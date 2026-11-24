-- Prove2me | Theorems.Thm_ULHC_TF_nbr_sub
-- name    : ULHC.TF.nbr_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:46:26.942061+00:00
-- url     : https://prove2.me/theorems/9d0ff077-6c40-41a8-8a3b-6254cce74fe1
-- title:
--   TF: nbr sub
-- statement:
--   The TF construction uses the nbr sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean#L206-L209
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean#L206-L209

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF

theorem ULHC.TF.nbr_sub {V : Finset Pt} {F : Finset Edge} (u : Pt) : nbr V F u ⊆ V := by sorry
