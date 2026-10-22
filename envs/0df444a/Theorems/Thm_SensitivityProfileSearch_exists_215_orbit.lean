-- Prove2me | Theorems.Thm_SensitivityProfileSearch_exists_215_orbit
-- name    : SensitivityProfileSearch.exists_215_orbit
-- status  : Open
-- author  : @dmilosch
-- created : 2026-10-21T22:17:11.021339+00:00
-- url     : https://prove2.me/theorems/c3770ecd-d493-4b1b-8809-72b030b1f260
-- title:
--   An arithmetic profile orbit at known labeling parameters crossing 2.15
-- statement:
--   Find a positive integer number of states, a positive period $\ell$, a natural number $R>1$, a periodic list of valid recipes, and two positive upper-triangular integer input matrices such that the deterministic profile orbit in `SensitivityProfileSearch` returns within factor $R$ after $\ell$ steps and
--
--   $$R^{43}<14055^{20\ell}.$$
--
--   Every positive tolerance used by a recipe must be at most five. The orbit uses the fixed parameters
--
--   $$d=7027,\quad t=24,\quad w=22,\quad (v_0,\ldots,v_5)=(24,31,38,44,50,55).$$
--
--   No graph or labeling must be constructed here: the simultaneous labeling theorem for the regular cyclic tournament at these parameters is already proved. No intermediate profile matrices, interval witnesses, or compatibility inequalities are supplied by the solver; all profiles are computed using the interval-minimum recurrence, and those obligations follow automatically from the recurrence and recipe validity.
--
--   This is an open sufficient-condition conjecture for `SensitivityProfileCycle.exists_215_certificate`. Neither a 2.15 orbit nor the adequacy of this fixed-parameter class is asserted to be known. The cited accepted construction achieves approximately 2.13082558; it does not establish this conjecture.
-- source:
--   Original deterministic interval-envelope reduction of the recursive profiles in accepted Prove2Me submission a9d25c46-43bd-4fb1-826b-0ed075b8cf0a, https://prove2.me/theorems/46659a00-722d-4dc9-b28e-ef02d6a0c9c2. Exact source components: SensitivitySourceLabeling14055Q5.shared_labeling_source_below_14055_q5_lll and SensitivityNQ.rawZeroSourceCombined/rawOne. Authors: yousofy with Codex; retains OpenAI/math, Robin Kothari with Codex, and earlier community attribution. The arithmetic 2.15 orbit conjecture is new and is not proved by that source.

import Definitions.Def_SensitivityProfileSearch

theorem SensitivityProfileSearch.exists_215_orbit :
    ∃ (n p radius : ℕ)
      (recipes : Fin (p+1) → SensitivityProfileCycle.Recipe (n+1))
      (initial : SensitivityProfileSearch.Profile (n+1)),
      1 < radius ∧ radius^43 < (14055^(p+1))^20 ∧
      SensitivityProfileSearch.PositiveUpper initial ∧
      (∀ d, (recipes d).Valid ∧
        ∀ i, 3 ≤ i.val → 0 < (recipes d).tol i → (recipes d).tol i < 6) ∧
      SensitivityProfileSearch.ReturnsWithin recipes initial radius := by sorry
