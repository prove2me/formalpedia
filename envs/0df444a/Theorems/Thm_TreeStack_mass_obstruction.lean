-- Prove2me | Theorems.Thm_TreeStack_mass_obstruction
-- name    : TreeStack.mass_obstruction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:49:57.451441+00:00
-- url     : https://prove2.me/theorems/1dbcb315-deeb-45c5-a340-898ae8d2ee91
-- title:
--   Tree Stack: mass obstruction
-- statement:
--   Exact mass of the explicit rooted obstruction.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L43-L83
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L43-L83

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.mass_obstruction (T : FiniteTree V) (r : V) :
    mass (obstruction T r) = rootEstimate T r - 1 := by sorry
