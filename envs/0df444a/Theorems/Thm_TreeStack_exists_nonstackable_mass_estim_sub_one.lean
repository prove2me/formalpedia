-- Prove2me | Theorems.Thm_TreeStack_exists_nonstackable_mass_estim_sub_one
-- name    : TreeStack.exists_nonstackable_mass_estim_sub_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:59:43.937801+00:00
-- url     : https://prove2.me/theorems/a116516d-debb-4ca0-afc1-1dbc061dba12
-- title:
--   Tree Stack: exists nonstackable mass estim sub one
-- statement:
--   At an estimator-maximizing root there is a non-stackable configuration of
--   exactly \`estim T - 1\` pebbles.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L1365-L1373
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L1365-L1373

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.exists_nonstackable_mass_estim_sub_one
    [Nontrivial V] (T : FiniteTree V) :
    ∃ C : Configuration V,
      mass C = estim T - 1 ∧
        ¬ Stackable T.graph C := by sorry
