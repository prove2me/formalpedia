-- Prove2me | Theorems.Thm_SZ_digitReal_ne
-- name    : SZ.digitReal_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:22:08.057371+00:00
-- url     : https://prove2.me/theorems/31659598-0513-453e-9da6-a139960ff01e
-- title:
--   SZ: digit Real ne
-- statement:
--   Two `{0,2}`-streams that first differ at index `i` give different reals.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L1026-L1034
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L1026-L1034

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.digitReal_ne {d d' : ℕ → ℤ} (h : IsDigits 3 d) (h' : IsDigits 3 d')
    (hd : ∀ j, d j = 0 ∨ d j = 2) (hd' : ∀ j, d' j = 0 ∨ d' j = 2)
    {i : ℕ} (hagree : ∀ j, j < i → d j = d' j) (hne : d i ≠ d' i) :
    digitReal 3 d ≠ digitReal 3 d' := by sorry
