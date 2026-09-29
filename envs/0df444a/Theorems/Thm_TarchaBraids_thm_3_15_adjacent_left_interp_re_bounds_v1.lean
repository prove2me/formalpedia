-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_adjacent_left_interp_re_bounds_v1
-- name    : TarchaBraids.thm_3_15_adjacent_left_interp_re_bounds_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T09:45:55.18252+00:00
-- url     : https://prove2.me/theorems/217a7556-064f-4982-b917-fbf8cbd647bb
-- title:
--   Tarcha 3.15 left interpolation stays in the local real strip
-- statement:
--   Throughout the left interpolation, all three distinguished local strands remain inside the real strip from i+1 to i+3.
-- source:
--   Reusable bounds extracted from the accepted left local-to-outside separation proof.

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_separation_interfaces_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_left_local_facts_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_outer_outside_facts_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_adjacent_left_interp_re_bounds_v1 :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      (∀ (u q : ℝ), 0 ≤ u → u ≤ 1 →
        ((i : ℕ) : ℝ) + 1 ≤ (leftOuterInterpFun n i j u q (strandIdx i)).re ∧
        (leftOuterInterpFun n i j u q (strandIdx i)).re ≤ ((i : ℕ) : ℝ) + 3) ∧
      (∀ (u q : ℝ), 0 ≤ u → u ≤ 1 →
        ((i : ℕ) : ℝ) + 1 ≤ (leftOuterInterpFun n i j u q (strandIdxSucc i)).re ∧
        (leftOuterInterpFun n i j u q (strandIdxSucc i)).re ≤ ((i : ℕ) : ℝ) + 3) ∧
      (∀ (u q : ℝ), 0 ≤ u → u ≤ 1 →
        ((i : ℕ) : ℝ) + 1 ≤ (leftOuterInterpFun n i j u q (strandIdxSucc j)).re ∧
        (leftOuterInterpFun n i j u q (strandIdxSucc j)).re ≤ ((i : ℕ) : ℝ) + 3) := by sorry

end TarchaBraids
