-- Prove2me | Theorems.Thm_Polynomial_Chebyshev_U_rank_one_root_localization
-- name    : Polynomial.Chebyshev.U_rank_one_root_localization
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-17T20:47:05.125611+00:00
-- url     : https://prove2.me/theorems/3b89ddea-f65b-4f3a-9f3b-f16e8de02c78
-- title:
--   Chebyshev polynomials: roots of an endpoint perturbation
-- statement:
--   Let $k\ge1$ and $a\ge0$. The polynomial
--   $$
--   U_{k+1}(t)-aU_k(t)
--   $$
--   has $k+1$ distinct real roots, which can be labeled $x_0>x_1>\cdots>x_k$. Their largest two satisfy
--   $$
--   x_1\le\cos\frac{\pi}{k+1},\qquad
--   x_0\ge\cos\frac{\pi}{k+2}.
--   $$
--   If $a\ge(k+2)/(k+1)$, then $x_0\ge1$. For any angle in the first interval between consecutive poles,
--   $$
--   \frac{\pi}{k+1}<\theta<\frac{2\pi}{k+1},
--   $$
--   one also has
--   $$
--   a<\frac{\sin((k+2)\theta)}{\sin((k+1)\theta)}
--   \quad\Longrightarrow\quad x_1\le\cos\theta.
--   $$
--   Here $U_j$ denotes the Chebyshev polynomial of the second kind. This is the scalar root-localization statement for its ratio, independently of any matrix realization.
-- source:
--   Andrew M. Childs, Lecture Notes on Quantum Algorithms, 17 April 2025, proof of Lemma 33.1, PDF pp. 182–183 (printed pp. 174–175), equations (33.21)–(33.23) and the discussion of simple poles and monotonicity after (33.22). https://www.cs.umd.edu/~amchilds/qa/qa.pdf

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
set_option autoImplicit false

theorem Polynomial.Chebyshev.U_rank_one_root_localization
    (k : ℕ) (hk : 1 ≤ k) (a : ℝ) (ha : 0 ≤ a) :
    ∃ x : Fin (k+1) → ℝ, StrictAnti x ∧
      (∀ i, (Polynomial.Chebyshev.U ℝ ((k+1 : ℕ) : ℤ)).eval (x i) =
        a * (Polynomial.Chebyshev.U ℝ (k : ℤ)).eval (x i)) ∧
      x ⟨1, by omega⟩ ≤ Real.cos (Real.pi / ((k : ℝ)+1)) ∧
      Real.cos (Real.pi / ((k : ℝ)+2)) ≤ x 0 ∧
      (((k : ℝ)+2) / ((k : ℝ)+1) ≤ a → 1 ≤ x 0) ∧
      (∀ θ ∈ Set.Ioo (Real.pi / ((k : ℝ)+1)) (2*Real.pi / ((k : ℝ)+1)),
        a < Real.sin (((k : ℝ)+2)*θ) / Real.sin (((k : ℝ)+1)*θ) →
        x ⟨1, by omega⟩ ≤ Real.cos θ) := by sorry
