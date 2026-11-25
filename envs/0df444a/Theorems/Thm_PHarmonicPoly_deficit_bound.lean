-- Prove2me | Theorems.Thm_PHarmonicPoly_deficit_bound
-- name    : PHarmonicPoly.deficit_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:46:54.011144+00:00
-- url     : https://prove2.me/theorems/6f2c3868-259a-5de3-89e2-e91fb8842228
-- title:
--   PHarmonic Poly: deficit bound
-- statement:
--   **Lemma 2.1 (deficit estimate).** Let `m ≥ 2` and let `T` be a real trigonometric
--   polynomial of degree at most `m` with `‖T‖∞ ≤ 1` and `T(0) = 1`. With `d = m² + T''(0)`,
--   `0 ≤ 1 + T(±π/m) ≤ d (1 - cos(π/m)) ≤ π² d / (2 m²)`.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/Solution.lean#L38-L47
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/Solution.lean#L38-L47

module
public import Definitions.Def_PHarmonicPoly
public import Definitions.Def_PHarmonicPoly_Solution
set_option autoImplicit false
@[expose] public section
public section
open PHarmonicPoly

theorem PHarmonicPoly.deficit_bound {m : ℕ} (hm : 2 ≤ m) {T : ℝ → ℝ} (hT : TrigPolyLe m T)
    (hbd : ∀ t : ℝ, |T t| ≤ 1) (h0 : T 0 = 1) :
    (0 ≤ 1 + T (Real.pi / m) ∧ 0 ≤ 1 + T (-(Real.pi / m)))
      ∧ (1 + T (Real.pi / m)
            ≤ ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) * (1 - Real.cos (Real.pi / m))
          ∧ 1 + T (-(Real.pi / m))
            ≤ ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) * (1 - Real.cos (Real.pi / m)))
      ∧ ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) * (1 - Real.cos (Real.pi / m))
          ≤ Real.pi ^ 2 * ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) / (2 * (m : ℝ) ^ 2) := by sorry
