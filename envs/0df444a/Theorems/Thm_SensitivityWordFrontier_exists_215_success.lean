-- Prove2me | Theorems.Thm_SensitivityWordFrontier_exists_215_success
-- name    : SensitivityWordFrontier.exists_215_success
-- status  : Disproved
-- author  : @dmilosch
-- created : 2026-10-22T18:48:46.420733+00:00
-- url     : https://prove2.me/theorems/9a9a585f-fba5-4c94-8a84-e0db00cfea98
-- title:
--   A positive-state exact frontier search succeeds at the 2.15 threshold
-- statement:
--   There is a positive state count and a finite depth at which the deterministic dominance-pruned profile search succeeds:
--
--   $$\exists n,k\in\mathbb N,\quad \mathrm{succeeds}(n+1,k)=\mathrm{true}.$$
--
--   Every search frontier is computed from the fixed all-ones initial profile using every valid letter in the finite tolerance alphabet. Success means that a retained profile has height $H$ satisfying
--
--   $$H^{43}<14055^{20k}.$$
--
--   This is the remaining open numerical existence problem. No successful state count, depth, profile, or recipe sequence is known from this submission. The separately proved search-correctness theorem makes this assertion equivalent to the original positive-state crossing-word conjecture; no stronger cutoff, bounded search horizon, or restriction to constant or periodic recipes is assumed.
-- source:
--   Original complete finite-search reduction of SensitivityProfileWord.exists_215_word, https://prove2.me/theorems/76888ed0-dff9-4b8d-b69f-5a603abeb564. Exact source definitions: SensitivityProfileWord.run, Admissible, Crosses215; SensitivityProfileSearch.step and envelope; SensitivityProfileCycle.Recipe.Valid. The recurrence originates in accepted submission a9d25c46-43bd-4fb1-826b-0ed075b8cf0a (yousofy with Codex), retaining OpenAI/math, Robin Kothari with Codex, and community attribution. The finite alphabet and dominance-pruning algorithm are new. No crossing witness or search-success bound is supplied or claimed to be known.

import Definitions.Def_SensitivityWordFrontier

theorem SensitivityWordFrontier.exists_215_success :
    ∃ n k : ℕ, SensitivityWordFrontier.succeeds (n+1) k = true := by sorry
