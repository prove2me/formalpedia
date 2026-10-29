-- Prove2me | Theorems.Thm_SensitivityProfileWord_exists_215_word
-- name    : SensitivityProfileWord.exists_215_word
-- status  : Disproved
-- author  : @dmilosch
-- created : 2026-10-21T22:38:39.707271+00:00
-- url     : https://prove2.me/theorems/76888ed0-dff9-4b8d-b69f-5a603abeb564
-- title:
--   A finite recipe sequence from all ones crossing the 2.15 threshold
-- statement:
--   Find a positive number of states and a nonempty finite sequence of valid recipes. Every positive tolerance used on an ordinary state must be at most five. Start from two matrices having ones on and above the diagonal and zeros below it; apply the fixed interval-envelope transfer map for the recipes in sequence.
--
--   If the sequence has length $L$ and the largest terminal matrix entry, clamped below by two, is $H$, the required condition is the exact integer inequality
--
--   $$H^{43}<14055^{20L}.$$
--
--   All graph parameters and defect cutoffs remain fixed at those of `SensitivityProfileSearch`. No initial matrices, intermediate profiles, interval witnesses, or radius need be guessed: the sequence determines them. The all-ones characterization proves that this search is complete for `SensitivityProfileSearch.exists_215_orbit`, allowing repetition of a successful cycle.
--
--   The existence of a crossing sequence remains open. No witness reaching 2.15 is supplied, and no bound on the necessary state count or word length is asserted.
-- source:
--   Original complete all-ones normalization of the deterministic recurrence in https://prove2.me/theorems/c3770ecd-d493-4b1b-8809-72b030b1f260 (SensitivityProfileSearch.exists_215_orbit), based on monotonicity, integer homogeneity, repeated recipe words, and absorption of fixed overhead by a strict power gap. The raw recurrence is from accepted submission a9d25c46-43bd-4fb1-826b-0ed075b8cf0a, SensitivityNQ.rawOne and rawZeroSourceCombined, by yousofy with Codex, retaining OpenAI/math, Robin Kothari with Codex, and community attribution. No crossing word is supplied or claimed to be known.

import Definitions.Def_SensitivityProfileWord

theorem SensitivityProfileWord.exists_215_word :
    ∃ (n : ℕ) (word : List (SensitivityProfileCycle.Recipe (n+1))),
      SensitivityProfileWord.Crosses215 word := by sorry
