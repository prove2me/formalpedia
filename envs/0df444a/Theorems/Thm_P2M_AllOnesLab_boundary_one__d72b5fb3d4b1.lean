-- Prove2me | Theorems.Thm_P2M_AllOnesLab_boundary_one__d72b5fb3d4b1
-- name    : P2M_AllOnesLab_boundary_one__d72b5fb3d4b1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:54:25.475198+00:00
-- url     : https://prove2.me/theorems/b77d9c6b-7ff5-46cf-a26f-62efc7184d9d
-- title:
--   P2 M All Ones Lab boundary one  d72b5fb3d4b1: P2 M All Ones Lab boundary one  d72b5fb3d4b1
-- statement:
--   Boundary: n = 1 fails. X + 1 is irreducible; X² + X = X (X + 1) is not.
--
--   Source: https://github.com/BrandonMYates/allones-comparator/blob/76f3a65407c45de21228824f7a41430acec473a4/AllOnesLab/Basic.lean#L144-L162
-- source:
--   https://github.com/BrandonMYates/allones-comparator/blob/76f3a65407c45de21228824f7a41430acec473a4/AllOnesLab/Basic.lean#L144-L162

import Definitions.Def_AllOnesLab_Defs
import Definitions.Def_AllOnesLab_Basic
set_option autoImplicit true
open Polynomial
open AllOnesLab

theorem P2M_AllOnesLab_boundary_one__d72b5fb3d4b1 : Irreducible (allOnes 1) ∧ ¬ Irreducible (allOnesP 1) := by sorry

alias «AllOnesLab».«boundary_one'» := P2M_AllOnesLab_boundary_one__d72b5fb3d4b1
