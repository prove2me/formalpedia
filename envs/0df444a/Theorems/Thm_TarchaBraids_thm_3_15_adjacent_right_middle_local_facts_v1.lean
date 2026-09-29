-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_adjacent_right_middle_local_facts_v1
-- name    : TarchaBraids.thm_3_15_adjacent_right_middle_local_facts_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T10:12:18.179773+00:00
-- url     : https://prove2.me/theorems/d53dc9f8-8d0a-4810-b307-125746a8538f
-- title:
--   Tarcha 3.15 right adjacent middle-phase local coordinate facts
-- statement:
--   In the middle phase of the right adjacent three-half-twist word, the three distinguished strands have the stated explicit coordinates.
-- source:
--   Middle phase extracted from the failed monolithic right-reflection child.

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_adjacent_right_middle_local_facts_v1 :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      (∀ (q : ℝ), ¬ q ≤ 1 / 2 → q ≤ 3 / 4 →
        rightBraidFun n i j q (strandIdx i) =
          twistPoint ((i : ℕ) + 3 / 2) (-1) (4 * q - 2)) ∧
      (∀ (q : ℝ), ¬ q ≤ 1 / 2 → q ≤ 3 / 4 →
        rightBraidFun n i j q (strandIdxSucc i) = ((((i : ℕ) : ℝ) + 3 : ℝ) : ℂ)) ∧
      (∀ (q : ℝ), ¬ q ≤ 1 / 2 → q ≤ 3 / 4 →
        rightBraidFun n i j q (strandIdxSucc j) =
          twistPoint ((i : ℕ) + 3 / 2) 1 (4 * q - 2)) := by sorry

end TarchaBraids
