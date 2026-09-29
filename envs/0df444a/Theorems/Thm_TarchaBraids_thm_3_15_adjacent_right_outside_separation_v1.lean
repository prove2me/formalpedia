-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_adjacent_right_outside_separation_v1
-- name    : TarchaBraids.thm_3_15_adjacent_right_outside_separation_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T10:58:02.88026+00:00
-- url     : https://prove2.me/theorems/ee100cba-8cf9-4366-96f5-2d9b32b10abd
-- title:
--   Tarcha 3.15 right interpolation distinguished-to-outside separation
-- statement:
--   Each of the three distinguished strands of the right interpolation remains distinct from every outside strand throughout the interpolation square.
-- source:
--   Derived from the right interpolation strip bounds and the accepted outside-strand coordinate facts.

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_outer_outside_facts_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_right_interp_re_bounds_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_adjacent_right_outside_separation_v1 :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      (∀ (u q : ℝ), 0 ≤ u → u ≤ 1 →
        ∀ (k : Fin n),
          (k : ℕ) ≠ (i : ℕ) →
          (k : ℕ) ≠ (i : ℕ) + 1 →
          (k : ℕ) ≠ (i : ℕ) + 2 →
          rightOuterInterpFun n i j u q (strandIdx i) ≠
            rightOuterInterpFun n i j u q k) ∧
      (∀ (u q : ℝ), 0 ≤ u → u ≤ 1 →
        ∀ (k : Fin n),
          (k : ℕ) ≠ (i : ℕ) →
          (k : ℕ) ≠ (i : ℕ) + 1 →
          (k : ℕ) ≠ (i : ℕ) + 2 →
          rightOuterInterpFun n i j u q (strandIdxSucc i) ≠
            rightOuterInterpFun n i j u q k) ∧
      (∀ (u q : ℝ), 0 ≤ u → u ≤ 1 →
        ∀ (k : Fin n),
          (k : ℕ) ≠ (i : ℕ) →
          (k : ℕ) ≠ (i : ℕ) + 1 →
          (k : ℕ) ≠ (i : ℕ) + 2 →
          rightOuterInterpFun n i j u q (strandIdxSucc j) ≠
            rightOuterInterpFun n i j u q k) := by sorry

end TarchaBraids
