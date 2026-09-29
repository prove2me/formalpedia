-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_adjacent_right_first_local_facts_v1
-- name    : TarchaBraids.thm_3_15_adjacent_right_first_local_facts_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T10:12:28.544228+00:00
-- url     : https://prove2.me/theorems/daf819dd-f287-4ee6-ae4d-7d3a064c2302
-- title:
--   Tarcha 3.15 right adjacent first-phase local coordinate facts
-- statement:
--   In the first phase of the right adjacent three-half-twist word, the three distinguished strands have the stated explicit coordinates.
-- source:
--   First phase extracted from the failed monolithic right-reflection child.

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_adjacent_right_first_local_facts_v1 :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      (∀ (q : ℝ), q ≤ 1 / 2 →
        rightBraidFun n i j q (strandIdx i) = ((((i : ℕ) : ℝ) + 1 : ℝ) : ℂ)) ∧
      (∀ (q : ℝ), q ≤ 1 / 2 →
        rightBraidFun n i j q (strandIdxSucc i) =
          twistPoint ((i : ℕ) + 5 / 2) (-1) (2 * q)) ∧
      (∀ (q : ℝ), q ≤ 1 / 2 →
        rightBraidFun n i j q (strandIdxSucc j) =
          twistPoint ((i : ℕ) + 5 / 2) 1 (2 * q)) := by sorry

end TarchaBraids
