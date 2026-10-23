-- Prove2me | Theorems.Thm_SensitivityWordFrontier_search_correct
-- name    : SensitivityWordFrontier.search_correct
-- status  : Proved
-- author  : @dmilosch
-- created : 2026-10-22T18:48:51.744773+00:00
-- url     : https://prove2.me/theorems/39c67854-b4b0-4292-b640-97e0bef4941e
-- title:
--   Dominance-pruned finite search is sound and complete at every depth
-- statement:
--   For every natural state count $N$ and depth $k$, the exact finite search succeeds if and only if there is an admissible crossing recipe word of exactly that length:
--
--   $$\mathrm{succeeds}(N,k)=\mathrm{true}
--   \iff \exists w,\quad |w|=k\ \land\ \mathrm{Crosses215}(w).$$
--
--   The search enumerates bounded letters and retains only profiles undominated in the componentwise order at each depth. This equivalence states both that every reported success has a single realizable admissible recipe sequence, and that pruning cannot discard all successful sequences. The finite alphabet preserves arbitrary admissible words by canonicalizing only unused tolerance fields.
--
--   No bound on the necessary depth or state count is imposed. At depth zero the search cannot succeed because height is clamped below by two. The theorem does not assert that any positive-state search succeeds.
-- source:
--   Original complete finite-search reduction of SensitivityProfileWord.exists_215_word, https://prove2.me/theorems/76888ed0-dff9-4b8d-b69f-5a603abeb564. Exact source definitions: SensitivityProfileWord.run, Admissible, Crosses215; SensitivityProfileSearch.step and envelope; SensitivityProfileCycle.Recipe.Valid. The recurrence originates in accepted submission a9d25c46-43bd-4fb1-826b-0ed075b8cf0a (yousofy with Codex), retaining OpenAI/math, Robin Kothari with Codex, and community attribution. The finite alphabet and dominance-pruning algorithm are new. No crossing witness or search-success bound is supplied or claimed to be known.

import Definitions.Def_SensitivityWordFrontier

theorem SensitivityWordFrontier.search_correct (n k : ℕ) :
    SensitivityWordFrontier.succeeds n k = true ↔
      ∃ word : List (SensitivityProfileCycle.Recipe n),
        word.length = k ∧ SensitivityProfileWord.Crosses215 word := by sorry
