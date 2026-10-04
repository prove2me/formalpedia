-- Prove2me | Theorems.Thm_PiIrrationality_six_node_polynomial_lipschitz
-- name    : PiIrrationality.six_node_polynomial_lipschitz
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-03T17:00:46.436009+00:00
-- url     : https://prove2.me/theorems/98650353-8c6c-4fd4-8012-82b1067487ce
-- title:
--   Six interpolation values control a polynomial’s Lipschitz constant
-- statement:
--   Let $v_0,\ldots,v_5$ be six distinct complex numbers. There is a constant $C>0$, depending only on these nodes, such that every complex polynomial $p$ of degree at most five and every real $B\ge0$ satisfying
--
--   $$|p(v_i)|\le B\quad(0\le i<6)$$
--
--   also satisfy
--
--   $$|p(a)-p(b)|\le CB|a-b|\qquad\text{whenever }|a|,|b|\le2.$$
--
--   The zero polynomial is included. The same constant works for all coefficient vectors, sample bounds and points in the closed disk. This is a reusable consequence of Lagrange interpolation, useful for converting bounds at fixed Hermite sampling points into a divided-difference estimate in the [π irrationality-measure goal](https://prove2.me/theorems/06d04e2f-c2ad-434c-a9ba-332f6e66279c).
-- source:
--   Standard consequence of Lagrange interpolation: Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, LinearAlgebra/Lagrange.lean, Lagrange.eq_interpolate; Analysis/Calculus/MeanValue.lean, Convex.norm_image_sub_le_of_norm_deriv_le; compactness of the closed complex disk. https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/Lagrange.lean . Supporting lemma for https://prove2.me/theorems/06d04e2f-c2ad-434c-a9ba-332f6e66279c.

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Polynomial Finset

theorem PiIrrationality.six_node_polynomial_lipschitz (v : Fin 6 → ℂ) (hv : Function.Injective v) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℂ[X]) (B : ℝ),
      p.degree < 6 → 0 ≤ B → (∀ i, ‖p.eval (v i)‖ ≤ B) →
      ∀ a b : ℂ, ‖a‖ ≤ 2 → ‖b‖ ≤ 2 →
        ‖p.eval a - p.eval b‖ ≤ C * B * ‖a-b‖ := by sorry
