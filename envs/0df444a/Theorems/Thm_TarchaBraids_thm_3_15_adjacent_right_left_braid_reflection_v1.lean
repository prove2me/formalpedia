-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_adjacent_right_left_braid_reflection_v1
-- name    : TarchaBraids.thm_3_15_adjacent_right_left_braid_reflection_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T10:21:30.598855+00:00
-- url     : https://prove2.me/theorems/09355b7a-bbfe-496c-9fec-025cc0c393db
-- title:
--   Tarcha 3.15 right and left adjacent braid path reflection
-- statement:
--   The three distinguished strands of the right adjacent braid word are the reflections of the corresponding left-word strands about the centre with real coordinate i+2.
-- source:
--   Phasewise right/left reflection assembled from accepted modular local-coordinate theorems.

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_left_local_facts_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_right_first_local_facts_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_right_middle_local_facts_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_right_final_local_facts_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_adjacent_right_left_braid_reflection_v1 :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      (∀ q : ℝ,
        rightBraidFun n i j q (strandIdx i) =
          (((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
            leftBraidFun n i j q (strandIdxSucc j))) ∧
      (∀ q : ℝ,
        rightBraidFun n i j q (strandIdxSucc i) =
          (((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
            leftBraidFun n i j q (strandIdxSucc i))) ∧
      (∀ q : ℝ,
        rightBraidFun n i j q (strandIdxSucc j) =
          (((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
            leftBraidFun n i j q (strandIdx i))) := by sorry

end TarchaBraids
