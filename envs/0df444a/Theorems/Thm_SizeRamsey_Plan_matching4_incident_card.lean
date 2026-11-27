-- Prove2me | Theorems.Thm_SizeRamsey_Plan_matching4_incident_card
-- name    : SizeRamsey.Plan.matching4_incident_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:24:45.538793+00:00
-- url     : https://prove2.me/theorems/c503c8fa-736d-5120-aea6-2c0131dbecbc
-- title:
--   Plan: matching4 incident card
-- statement:
--   The Plan construction uses the matching4 incident card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/ColoringBase.lean#L39-L63
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/ColoringBase.lean#L39-L63

module
public import Definitions.Def_SizeRamsey_Shared
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_ColoringBase
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan

theorem SizeRamsey.Plan.matching4_incident_card {V : Type*}
    (F : SimpleGraph V) (S : Finset V)
    (h : HasMatching4 (incidentRed F S)) :
    4 ≤ S.card := by sorry
