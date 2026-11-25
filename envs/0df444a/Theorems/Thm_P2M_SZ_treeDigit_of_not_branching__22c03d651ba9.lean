-- Prove2me | Theorems.Thm_P2M_SZ_treeDigit_of_not_branching__22c03d651ba9
-- name    : P2M_SZ_treeDigit_of_not_branching__22c03d651ba9
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:18:30.942269+00:00
-- url     : https://prove2.me/theorems/a8582e9b-25b9-4549-bde8-6af78d02324e
-- title:
--   P2 M SZ tree Digit of not branching  22c03d651ba9: P2 M SZ tree Digit of not branching  22c03d651ba9
-- statement:
--   The P2 M SZ tree Digit of not branching  22c03d651ba9 construction uses the P2 M SZ tree Digit of not branching  22c03d651ba9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L703-L706
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L703-L706

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem P2M_SZ_treeDigit_of_not_branching__22c03d651ba9 (β : ℕ → Bool) {N : ℕ}
    (hno : ∀ i, ¬ Branching (node β (N + i))) (j : ℕ) :
    treeDigit β (N + j) = gDigit (node β N).st j := by sorry

alias «SZ».«treeDigit_of_not_branching'» := P2M_SZ_treeDigit_of_not_branching__22c03d651ba9
