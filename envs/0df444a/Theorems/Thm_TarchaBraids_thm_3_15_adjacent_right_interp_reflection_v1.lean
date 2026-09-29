-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_adjacent_right_interp_reflection_v1
-- name    : TarchaBraids.thm_3_15_adjacent_right_interp_reflection_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T09:52:30.219238+00:00
-- url     : https://prove2.me/theorems/b4b2edea-be70-4bf0-8c70-52e1ae1214b5
-- title:
--   Tarcha 3.15 right interpolation is the reflection of the left interpolation
-- statement:
--   For adjacent strands, the three distinguished coordinates of the right interpolation are obtained by reflecting the corresponding left interpolation coordinates across the midpoint line at real coordinate i+2.
-- source:
--   Symmetry layer extracted from Tarcha's explicit adjacent Artin relation proof.

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_adjacent_right_interp_reflection_v1 :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      (∀ (u q : ℝ),
        rightOuterInterpFun n i j u q (strandIdx i) =
          (((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
            leftOuterInterpFun n i j u q (strandIdxSucc j))) ∧
      (∀ (u q : ℝ),
        rightOuterInterpFun n i j u q (strandIdxSucc i) =
          (((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
            leftOuterInterpFun n i j u q (strandIdxSucc i))) ∧
      (∀ (u q : ℝ),
        rightOuterInterpFun n i j u q (strandIdxSucc j) =
          (((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
            leftOuterInterpFun n i j u q (strandIdx i))) := by sorry

end TarchaBraids
