-- Prove2me | Theorems.Thm_PalomarNewtonian_globalCubicSensitivityAndOptimality
-- name    : PalomarNewtonian.globalCubicSensitivityAndOptimality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T04:03:10.247278+00:00
-- url     : https://prove2.me/theorems/df3a9f17-7a7e-4a09-95dc-1d59b41b8dff
-- title:
--   Palomar Newtonian: global Cubic Sensitivity And Optimality
-- statement:
--   Global Newtonian sensitivity for arbitrary finite masses and source
--   positions, and exact universality of the coefficient. All distances are
--   measured in the Cartesian maximum norm; the gravitational field uses
--   the physical Euclidean radius. The second conjunct proves optimality
--   universally over configurations (already N=1 suffices), not
--   optimality separately for every fixed N and every fixed mass layout.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/Solution.lean#L175-L249
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/Solution.lean#L175-L249

module
public import Definitions.Def_NewtonianLipschitz
public import Definitions.Def_NewtonianLipschitz_Solution_74f12a8
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem PalomarNewtonian.globalCubicSensitivityAndOptimality
    (t : ℝ)
    (htlow : (9 / 50 : ℝ) ≤ t)
    (hthigh : t ≤ (1 / 5 : ℝ))
    (htcubic : 2 * t ^ 3 - 8 * t ^ 2 - 4 * t + 1 = 0) :
    (∀ (n : ℕ) (G M d : ℝ)
      (m : Fin n → ℝ) (a : Fin n → Fin 3 → ℝ)
      (P Q : Fin 3 → ℝ),
      0 ≤ G →
      0 ≤ M →
      0 < d →
      (∀ i : Fin n, 0 ≤ m i ∧ m i ≤ M) →
      (∀ i : Fin n, d ≤ ‖P - a i‖ ∧ d ≤ ‖Q - a i‖) →
      let g : (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
        fun z =>
          ∑ i : Fin n,
            (-(G * m i) /
              (Real.sqrt
                ((z 0 - a i 0) ^ 2 +
                 (z 1 - a i 1) ^ 2 +
                 (z 2 - a i 2) ^ 2)) ^ 3) • (z - a i)
      ‖g P - g Q‖ ≤
        ((n : ℝ) * G * M *
          ((2 + 6 * t - 2 * t ^ 2) /
            (Real.sqrt (1 + 2 * t ^ 2)) ^ 5) / d ^ 3) *
          ‖P - Q‖) ∧
    (∀ K : ℝ,
      (∀ P Q : Fin 3 → ℝ,
        (1 : ℝ) ≤ ‖P‖ →
        (1 : ℝ) ≤ ‖Q‖ →
        ‖(-(1 : ℝ) /
            (Real.sqrt (P 0 ^ 2 + P 1 ^ 2 + P 2 ^ 2)) ^ 3) • P -
          (-(1 : ℝ) /
            (Real.sqrt (Q 0 ^ 2 + Q 1 ^ 2 + Q 2 ^ 2)) ^ 3) • Q‖ ≤
          K * ‖P - Q‖) ↔
      (2 + 6 * t - 2 * t ^ 2) /
        (Real.sqrt (1 + 2 * t ^ 2)) ^ 5 ≤ K) := by sorry
