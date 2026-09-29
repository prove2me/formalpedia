-- Prove2me | Theorems.Thm_Transcendence_expPoly_grid_estimate
-- name    : Transcendence.expPoly_grid_estimate
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-27T07:58:20.872874+00:00
-- url     : https://prove2.me/theorems/707e3c54-a49b-4eac-9d9e-72e16ae0627b
-- title:
--   A Cauchy estimate for an exponential polynomial that vanishes on a grid
-- statement:
--   Let $y_1, \dots, y_l \in \mathbb{C}$ be linearly independent over $\mathbb{Q}$, and let $F(z) = \sum_{k \in s} c_k z^{e_k} e^{\omega_k z}$ with $|\omega_k| \le W$ and $e_k \le E$ for all $k$. Let $t_j \le A_j$ be natural numbers, and suppose that $F$ vanishes to order at least $n$ at every grid point $\sum_j m'_j y_j$ with $m'_j < t_j$. Let $u \ge 2$ and $Z \ge \big(\sum_j A_j |y_j| + 1\big)(u + 1)$. Then at every point $w = \sum_j m_j y_j$ with $m_j < A_j$, and for every $r$,
--
--   $$|F^{(r)}(w)| \le 2\, r!\, (u - 1)^{-n \prod_j t_j} \Big(\sum_{k \in s} |c_k|\Big) Z^{E} e^{WZ}.$$
--
--   This is the analytic step of the extrapolation arguments: the $\prod_j t_j$ grid points are distinct because the $y_j$ are $\mathbb{Q}$-linearly independent, and the Cauchy estimate with zeros (`FourExp.cauchy_estimate_with_zeros`) is applied on a circle of radius $(\rho + 1)u$ about $w$, where $\rho = \sum_j A_j |y_j|$.
-- source:
--   The analytic step of the extrapolation in the proof of Lemma 5 of M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, and of the six exponentials theorem (S. Lang, Introduction to Transcendental Numbers, 1966, Ch. 2); it rests on the estimate of M. Waldschmidt, Indépendance algébrique des valeurs de la fonction exponentielle, Bull. Soc. Math. France 99 (1971), 285–304, §4, inequality (4.3). Formal proof: Diaz modulus mission, 27 September 2026 (C. Perassi).

import Mathlib

namespace Transcendence

theorem expPoly_grid_estimate {ι κ : Type*} [Fintype ι] (y : ι → ℂ)
    (hy : LinearIndependent ℚ y) (s : Finset κ) (c ω : κ → ℂ) (e : κ → ℕ) (F : ℂ → ℂ)
    (hF : ∀ z, F z = ∑ k ∈ s, c k * z ^ e k * Complex.exp (ω k * z))
    (W : ℝ) (E : ℕ) (hω : ∀ k ∈ s, ‖ω k‖ ≤ W) (he : ∀ k ∈ s, e k ≤ E)
    (t A : ι → ℕ) (htA : ∀ j, t j ≤ A j) (n : ℕ)
    (hvan : ∀ m : ι → ℕ, (∀ j, m j < t j) → ∀ i < n,
      iteratedDeriv i F (∑ j, (m j : ℂ) * y j) = 0)
    (u Z : ℝ) (hu : 2 ≤ u) (hZ : (∑ j, (A j : ℝ) * ‖y j‖ + 1) * (u + 1) ≤ Z)
    (m : ι → ℕ) (hm : ∀ j, m j < A j) (r : ℕ) :
    ‖iteratedDeriv r F (∑ j, (m j : ℂ) * y j)‖
      ≤ (r.factorial : ℝ) * 2 * (1 / (u - 1)) ^ ((∏ j, t j) * n) *
        ((∑ k ∈ s, ‖c k‖) * Z ^ E * Real.exp (W * Z)) := by
  sorry

end Transcendence
