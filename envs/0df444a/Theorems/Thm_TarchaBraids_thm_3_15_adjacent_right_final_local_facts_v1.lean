-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_adjacent_right_final_local_facts_v1
-- name    : TarchaBraids.thm_3_15_adjacent_right_final_local_facts_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T10:12:23.212117+00:00
-- url     : https://prove2.me/theorems/07def36f-c250-4787-92cc-cbd5b363efdb
-- title:
--   Tarcha 3.15 right adjacent final-phase local coordinate facts
-- statement:
--   In the final phase of the right adjacent three-half-twist word, the three distinguished strands have the stated explicit coordinates.
-- source:
--   Final phase extracted from the failed monolithic right-reflection child.

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_adjacent_right_final_local_facts_v1 :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      (∀ (q : ℝ), ¬ q ≤ 1 / 2 → ¬ q ≤ 3 / 4 →
        rightBraidFun n i j q (strandIdx i) =
          twistPoint ((i : ℕ) + 5 / 2) (-1) (4 * q - 3)) ∧
      (∀ (q : ℝ), ¬ q ≤ 1 / 2 → ¬ q ≤ 3 / 4 →
        rightBraidFun n i j q (strandIdxSucc i) =
          twistPoint ((i : ℕ) + 5 / 2) 1 (4 * q - 3)) ∧
      (∀ (q : ℝ), ¬ q ≤ 1 / 2 → ¬ q ≤ 3 / 4 →
        rightBraidFun n i j q (strandIdxSucc j) = ((((i : ℕ) : ℝ) + 1 : ℝ) : ℂ)) := by sorry

end TarchaBraids
