-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_2_6_lambda_continuous
-- name    : Scott1976.DataTypesAsLattices.theorem_2_6_lambda_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:52.611219+00:00
-- url     : https://prove2.me/theorems/aa3c30bf-9669-5eea-b0fd-946b55bc2833
-- title:
--   Data Types As Lattices: theorem 2 6 lambda continuous
-- statement:
--   LAMBDA-definable maps (in one free variable) are continuous, so
--   clause (iii) of Theorem 2.6 lands in the setting of (i)–(ii).
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Computability.lean#L45-L47
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Computability.lean#L45-L47

import Mathlib.Computability.RE
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Computability
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_2_6_lambda_continuous (t : Term) :
    IsScottContinuous (fun v => interp t (envSet (fun _ => botElem) 0 v)) := by sorry
