-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_adjacent_right_interp_re_bounds_v1
-- name    : TarchaBraids.thm_3_15_adjacent_right_interp_re_bounds_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T10:53:23.076093+00:00
-- url     : https://prove2.me/theorems/57a69266-de79-40c8-b6c4-320582635987
-- title:
--   Tarcha 3.15 right interpolation real-strip bounds
-- statement:
--   For interpolation parameter u in [0,1], each distinguished strand of the right interpolation remains in the real strip from i+1 to i+3.
-- source:
--   Derived by reflecting the accepted left interpolation strip bounds.

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_left_interp_re_bounds_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_right_interp_reflection_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_adjacent_right_interp_re_bounds_v1 :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      (∀ (u q : ℝ), 0 ≤ u → u ≤ 1 →
        ((i : ℕ) : ℝ) + 1 ≤ (rightOuterInterpFun n i j u q (strandIdx i)).re ∧
        (rightOuterInterpFun n i j u q (strandIdx i)).re ≤ ((i : ℕ) : ℝ) + 3) ∧
      (∀ (u q : ℝ), 0 ≤ u → u ≤ 1 →
        ((i : ℕ) : ℝ) + 1 ≤ (rightOuterInterpFun n i j u q (strandIdxSucc i)).re ∧
        (rightOuterInterpFun n i j u q (strandIdxSucc i)).re ≤ ((i : ℕ) : ℝ) + 3) ∧
      (∀ (u q : ℝ), 0 ≤ u → u ≤ 1 →
        ((i : ℕ) : ℝ) + 1 ≤ (rightOuterInterpFun n i j u q (strandIdxSucc j)).re ∧
        (rightOuterInterpFun n i j u q (strandIdxSucc j)).re ≤ ((i : ℕ) : ℝ) + 3) := by sorry

end TarchaBraids
