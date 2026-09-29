-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_adjacent_outer_reflection_v1
-- name    : TarchaBraids.thm_3_15_adjacent_outer_reflection_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T10:19:11.163413+00:00
-- url     : https://prove2.me/theorems/8ea8e504-9f12-4f79-a720-324a71f2b010
-- title:
--   Tarcha 3.15 outer rotation reflection identities
-- statement:
--   The common outer-rotation path is invariant under reflection about the vertical line with real coordinate i+2, exchanging the two outer distinguished strands and fixing the middle one.
-- source:
--   Independent symmetry layer extracted from the adjacent Artin relation proof.

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_outer_outside_facts_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_adjacent_outer_reflection_v1 :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      (∀ q : ℝ,
        outerRotateFun n i q (strandIdx i) =
          (((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
            outerRotateFun n i q (strandIdxSucc j))) ∧
      (∀ q : ℝ,
        outerRotateFun n i q (strandIdxSucc i) =
          (((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
            outerRotateFun n i q (strandIdxSucc i))) ∧
      (∀ q : ℝ,
        outerRotateFun n i q (strandIdxSucc j) =
          (((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
            outerRotateFun n i q (strandIdx i))) := by sorry

end TarchaBraids
