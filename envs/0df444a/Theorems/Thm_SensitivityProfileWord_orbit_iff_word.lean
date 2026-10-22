-- Prove2me | Theorems.Thm_SensitivityProfileWord_orbit_iff_word
-- name    : SensitivityProfileWord.orbit_iff_word
-- status  : Proved
-- author  : @dmilosch
-- created : 2026-10-21T22:38:21.847681+00:00
-- url     : https://prove2.me/theorems/ce0348ca-6a7e-4ada-a2fa-153d9cf45aa3
-- title:
--   All-ones recipe search is complete for the 2.15 orbit criterion
-- statement:
--   The positive-profile orbit criterion of `SensitivityProfileSearch.exists_215_orbit` is equivalent to the existence of a positive number of states and a finite recipe word satisfying `SensitivityProfileWord.Crosses215`.
--
--   Thus a certificate with arbitrary positive integer initial matrices, a positive period $L$, and an integer return factor $R>1$ satisfying
--
--   $$R^{43}<14055^{20L}$$
--
--   exists if and only if a nonempty admissible recipe sequence, started from the fixed all-ones upper-triangular profile, has terminal height $H$ satisfying
--
--   $$H^{43}<14055^{20L'}.$$
--
--   The new sequence may be longer than the original period. The equivalence preserves the allowed state counts, recipes, and tolerance bounds. It removes all freely chosen initial profile entries and the freely chosen radius from the search, without requiring a new restriction on the family of constructions. This equivalence does not assert that either side has a witness.
-- source:
--   Original complete all-ones normalization of the deterministic recurrence in https://prove2.me/theorems/c3770ecd-d493-4b1b-8809-72b030b1f260 (SensitivityProfileSearch.exists_215_orbit), based on monotonicity, integer homogeneity, repeated recipe words, and absorption of fixed overhead by a strict power gap. The raw recurrence is from accepted submission a9d25c46-43bd-4fb1-826b-0ed075b8cf0a, SensitivityNQ.rawOne and rawZeroSourceCombined, by yousofy with Codex, retaining OpenAI/math, Robin Kothari with Codex, and community attribution. No crossing word is supplied or claimed to be known.

import Definitions.Def_SensitivityProfileWord

theorem SensitivityProfileWord.orbit_iff_word :
    (∃ (n p radius : ℕ)
      (recipes : Fin (p+1) → SensitivityProfileCycle.Recipe (n+1))
      (initial : SensitivityProfileSearch.Profile (n+1)),
      1 < radius ∧ radius^43 < (14055^(p+1))^20 ∧
      SensitivityProfileSearch.PositiveUpper initial ∧
      (∀ d, (recipes d).Valid ∧
        ∀ i, 3 ≤ i.val → 0 < (recipes d).tol i → (recipes d).tol i < 6) ∧
      SensitivityProfileSearch.ReturnsWithin recipes initial radius) ↔
    ∃ (n : ℕ) (word : List (SensitivityProfileCycle.Recipe (n+1))),
      SensitivityProfileWord.Crosses215 word := by sorry
