-- Prove2me | Theorems.Thm_SZ_digitReal_lt_of_zero_two
-- name    : SZ.digitReal_lt_of_zero_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:22:00.570311+00:00
-- url     : https://prove2.me/theorems/ffe6952f-bee9-4931-87f2-a783640f2dd8
-- title:
--   SZ: digit Real lt of zero two
-- statement:
--   A `0` where the other stream has a `2`, with the streams agreeing before, puts the reals
--   a full `3^{-(i+1)}` apart.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L1007-L1023
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L1007-L1023

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.digitReal_lt_of_zero_two {d d' : ℕ → ℤ} (h : IsDigits 3 d) (h' : IsDigits 3 d')
    {i : ℕ} (hagree : ∀ j, j < i → d j = d' j) (h0 : d i = 0) (h2 : d' i = 2) :
    digitReal 3 d < digitReal 3 d' := by sorry
