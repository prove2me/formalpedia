-- Prove2me | Theorems.Thm_SoficGroups_KunResidualRetainedSelection_matchedRetained_parts_eventually_nonempty_of_discard
-- name    : SoficGroups.KunResidualRetainedSelection.matchedRetained_parts_eventually_nonempty_of_discard
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:29.358829+00:00
-- url     : https://prove2.me/theorems/b5b50a4b-cf1f-4abc-ad14-ea1e5c64a455
-- title:
--   SoficGroups.KunResidualRetainedSelection.matchedRetained_parts_eventually_nonempty_of_discard
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunResidualRetainedSelection
open Filter Topology
open scoped BigOperators Pointwise symmDiff

theorem SoficGroups.KunResidualRetainedSelection.matchedRetained_parts_eventually_nonempty_of_discard
    {V : ℕ → Type*} [∀ n, DecidableEq (V n)]
    (U : ∀ n, Finset (V n)) (hU : ∀ n, (U n).Nonempty)
    (R : ∀ n, Finset (Finset (V n)))
    (hdiscard : Tendsto
      (fun n =>
        (((U n \ SoficGroups.matchedRetainedSupport (R n)).card : ℝ) /
          (U n).card)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, (R n).Nonempty := by sorry
