-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_2_6_combinatory_zero
-- name    : Scott1976.DataTypesAsLattices.theorem_2_6_combinatory_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:54.509235+00:00
-- url     : https://prove2.me/theorems/95898202-84ac-5dd2-8417-4a47405df6ee
-- title:
--   Data Types As Lattices: theorem 2 6 combinatory zero
-- statement:
--   Combinatory elements are generated from the six constants, matching
--   the LAMBDA-definable closed terms of Theorem 2.4.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Computability.lean#L51-L52
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Computability.lean#L51-L52

import Mathlib.Computability.RE
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Computability
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_2_6_combinatory_zero : IsLambdaDefinable zeroC := by sorry
