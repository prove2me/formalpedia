-- Prove2me | Theorems.Thm_SizeRamsey_Plan_transversal_no_blue_square
-- name    : SizeRamsey.Plan.transversal_no_blue_square
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:24:52.037123+00:00
-- url     : https://prove2.me/theorems/968fda9b-5501-505e-b017-33837627e2d5
-- title:
--   Plan: transversal no blue square
-- statement:
--   The Plan construction uses the transversal no blue square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/ColoringBase.lean#L65-L79
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/ColoringBase.lean#L65-L79

module
public import Definitions.Def_SizeRamsey_Shared
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_ColoringBase
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan

theorem SizeRamsey.Plan.transversal_no_blue_square {V : Type*}
    (F : SimpleGraph V) (S : Finset V)
    (h : c4Transversal F S) :
    ¬ HasC4 (F \ incidentRed F S) := by sorry
