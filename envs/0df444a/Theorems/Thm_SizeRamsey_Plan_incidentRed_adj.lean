-- Prove2me | Theorems.Thm_SizeRamsey_Plan_incidentRed_adj
-- name    : SizeRamsey.Plan.incidentRed_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:19:18.419687+00:00
-- url     : https://prove2.me/theorems/87bb2986-d294-415b-81a8-5e7cb1a45888
-- title:
--   Plan: incident Red adj
-- statement:
--   The Plan construction uses the incident Red adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/ColoringBase.lean#L27-L37
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/ColoringBase.lean#L27-L37

module
public import Definitions.Def_SizeRamsey_Shared
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_ColoringBase
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan

theorem SizeRamsey.Plan.incidentRed_adj {V : Type*}
    (F : SimpleGraph V) (S : Finset V) (u v : V) :
    (incidentRed F S).Adj u v ↔
      F.Adj u v ∧ (u ∈ S ∨ v ∈ S) := by sorry
