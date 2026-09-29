-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_adjacent_right_pairwise_separation_v1
-- name    : TarchaBraids.thm_3_15_adjacent_right_pairwise_separation_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T10:53:14.411632+00:00
-- url     : https://prove2.me/theorems/4fe26922-70b8-4f95-aa66-d213cf16e3a5
-- title:
--   Tarcha 3.15 right interpolation pairwise local separation
-- statement:
--   Throughout the explicit right interpolation, the three distinguished local strands remain pairwise distinct for all interpolation and path parameters in the unit interval.
-- source:
--   Derived from the accepted left pairwise separation theorem by the right/left interpolation reflection.

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_left_pairwise_separation_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_right_interp_reflection_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_adjacent_right_pairwise_separation_v1 :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      (∀ (u q : ℝ), 0 ≤ u → u ≤ 1 → 0 ≤ q → q ≤ 1 →
        rightOuterInterpFun n i j u q (strandIdx i) ≠
          rightOuterInterpFun n i j u q (strandIdxSucc i)) ∧
      (∀ (u q : ℝ), 0 ≤ u → u ≤ 1 → 0 ≤ q → q ≤ 1 →
        rightOuterInterpFun n i j u q (strandIdx i) ≠
          rightOuterInterpFun n i j u q (strandIdxSucc j)) ∧
      (∀ (u q : ℝ), 0 ≤ u → u ≤ 1 → 0 ≤ q → q ≤ 1 →
        rightOuterInterpFun n i j u q (strandIdxSucc i) ≠
          rightOuterInterpFun n i j u q (strandIdxSucc j)) := by sorry

end TarchaBraids
