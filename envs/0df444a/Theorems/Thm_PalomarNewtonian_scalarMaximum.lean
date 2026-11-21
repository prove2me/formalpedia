-- Prove2me | Theorems.Thm_PalomarNewtonian_scalarMaximum
-- name    : PalomarNewtonian.scalarMaximum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T04:02:58.10158+00:00
-- url     : https://prove2.me/theorems/c1afeef2-a00b-4149-893b-bb63df05b8d8
-- title:
--   Palomar Newtonian: scalar Maximum
-- statement:
--   The stationary cubic has one root in the rational bracket. At that
--   root the stated exact scalar coefficient is maximal on [0,1].
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/Solution.lean#L139-L167
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/Solution.lean#L139-L167

module
public import Definitions.Def_NewtonianLipschitz
public import Definitions.Def_NewtonianLipschitz_Solution_74f12a8
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem PalomarNewtonian.scalarMaximum :
    ∃ t : ℝ,
      (9 / 50 : ℝ) ≤ t ∧
      t ≤ (1 / 5 : ℝ) ∧
      2 * t ^ 3 - 8 * t ^ 2 - 4 * t + 1 = 0 ∧
      (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
        (2 + 6 * s - 2 * s ^ 2) /
          (Real.sqrt (1 + 2 * s ^ 2)) ^ 5 ≤
        (2 + 6 * t - 2 * t ^ 2) /
          (Real.sqrt (1 + 2 * t ^ 2)) ^ 5) ∧
      (∀ u : ℝ,
        (9 / 50 : ℝ) ≤ u →
        u ≤ (1 / 5 : ℝ) →
        2 * u ^ 3 - 8 * u ^ 2 - 4 * u + 1 = 0 →
        u = t) := by sorry
