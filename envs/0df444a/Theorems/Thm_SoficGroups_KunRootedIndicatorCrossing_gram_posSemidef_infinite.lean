-- Prove2me | Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_gram_posSemidef_infinite
-- name    : SoficGroups.KunRootedIndicatorCrossing.gram_posSemidef_infinite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:25.142856+00:00
-- url     : https://prove2.me/theorems/39abe1cf-9dc8-4c3c-b70e-0411d3747675
-- title:
--   SoficGroups.KunRootedIndicatorCrossing.gram_posSemidef_infinite
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology

theorem SoficGroups.KunRootedIndicatorCrossing.gram_posSemidef_infinite
    {I H : Type*} [SeminormedAddCommGroup H]
    [InnerProductSpace ℂ H] (v : I → H) :
    (Matrix.gram ℂ v).PosSemidef := by sorry
