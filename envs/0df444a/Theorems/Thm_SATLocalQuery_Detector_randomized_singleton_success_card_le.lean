-- Prove2me | Theorems.Thm_SATLocalQuery_Detector_randomized_singleton_success_card_le
-- name    : SATLocalQuery.Detector.randomized_singleton_success_card_le
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T21:46:38.355315+00:00
-- url     : https://prove2.me/theorems/6df003ee-1100-5761-aec4-80be84d89441
-- title:
--   Number of successful guesses in randomized adaptive singleton search
-- statement:
--   Let a finite set of seeds index adaptive detectors that query an unknown Boolean oracle and output a guessed target or no guess. Assume each detector makes at most q queries when run with the identically false oracle. Over all ordered seed and target pairs, at most the number of seeds times q plus one, with q plus one taken as a factor, lead to an exact output guess when the oracle is true only at that target.
-- source:
--   The oracle transcript argument for searching a singleton.

import Definitions.Def_SATLocalQueryDetector

open SATLocalQuery SATLocalQuery.Detector

theorem SATLocalQuery.Detector.randomized_singleton_success_card_le {I R : Type*}
    [Fintype R] [DecidableEq R] [Fintype I] [DecidableEq I]
    (D : R → Detector I (Option I)) (q : ℕ)
    (short : ∀ r, (calls (fun _ => false) (D r)).length ≤ q) :
    (Finset.univ.filter fun p : R × I => run (onlyAt p.2) (D p.1) = some p.2).card ≤
      Fintype.card R * (q+1) := by sorry
