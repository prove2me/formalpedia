-- Prove2me | Theorems.Thm_SoficGroups_SourceCommonOffsetMidrankEnergy_componentSizeComparison_of_not_mem
-- name    : SoficGroups.SourceCommonOffsetMidrankEnergy.componentSizeComparison_of_not_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:30.418361+00:00
-- url     : https://prove2.me/theorems/42ce219e-d62d-499f-9a27-60a71f201ff9
-- title:
--   SoficGroups.SourceCommonOffsetMidrankEnergy.componentSizeComparison_of_not_mem
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCommonOffsetMidrankEnergy
open Filter Topology
open scoped BigOperators

theorem SoficGroups.SourceCommonOffsetMidrankEnergy.componentSizeComparison_of_not_mem
    {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (Q : Finpartition (Finset.univ : Finset V))
    (p : ι → Equiv.Perm V) (eta : ℝ)
    (i : ι) (x : V)
    (hx : (i, x) ∉ componentSizeComparisonBad Q p eta) :
    (1 - eta) * realComponentSize Q x ≤
      realComponentSize Q (p i x) := by sorry
