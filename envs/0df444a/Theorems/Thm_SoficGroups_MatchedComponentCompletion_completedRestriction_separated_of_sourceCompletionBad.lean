-- Prove2me | Theorems.Thm_SoficGroups_MatchedComponentCompletion_completedRestriction_separated_of_sourceCompletionBad
-- name    : SoficGroups.MatchedComponentCompletion.completedRestriction_separated_of_sourceCompletionBad
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.241177+00:00
-- url     : https://prove2.me/theorems/950b5abf-cbda-48cc-8a43-9ce7dcc17391
-- title:
--   SoficGroups.MatchedComponentCompletion.completedRestriction_separated_of_sourceCompletionBad
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.MatchedComponentCompletion
open scoped BigOperators

theorem SoficGroups.MatchedComponentCompletion.completedRestriction_separated_of_sourceCompletionBad
    {V ι J : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V) (p : J → Equiv.Perm V)
    (F : Finset J) (Z : Finset V) (hZ : Z.Nonempty)
    (hbad : 5 * (sourceCompletionBad σ p F Z).card ≤ Z.card)
    {j k : J} (hj : j ∈ F) (hk : k ∈ F) (hne : j ≠ k) :
    Fintype.card {x : V // x ∈ Z} <
      5 * SoficGroups.permutationDistance
        (completedRestriction (p j) Z) (completedRestriction (p k) Z) := by sorry
