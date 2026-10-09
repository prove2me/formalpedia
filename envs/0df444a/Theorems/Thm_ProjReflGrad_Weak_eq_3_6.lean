-- Prove2me | Theorems.Thm_ProjReflGrad_Weak_eq_3_6
-- name    : ProjReflGrad.Weak.eq_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:16:11.775849+00:00
-- url     : https://prove2.me/theorems/39ce89f4-3f70-47b9-91d2-0083d21db0b1
-- title:
--   (3.6), proof of Theorem 3.2, p. 5 — the Lyapunov-type inequality for z ∈ S, n ≥ 2
-- statement:
--   In the setting of Lemma 3.1, assume in addition $0<\lambda<(\sqrt2-1)/L$, so that $1-\sqrt2\lambda L>\lambda L$. Then for every $z\in S$ and every $n\ge2$
--   $$\|x_{n+1}-z\|^2+\lambda L\|x_{n+1}-y_n\|^2+2\lambda\langle F(z),x_n-z\rangle\le\|x_n-z\|^2+\lambda L\|x_n-y_{n-1}\|^2+2\lambda\langle F(z),x_{n-1}-z\rangle-\big(1-\lambda L(1+\sqrt2)\big)\|x_n-x_{n-1}\|^2 .$$
--
--   With $a_n=\|x_n-z\|^2+\lambda L\|x_n-y_{n-1}\|^2+2\lambda\langle F(z),x_{n-1}-z\rangle$ and $b_n=(1-\lambda L(1+\sqrt2))\|x_n-x_{n-1}\|^2$ this reads $a_{n+1}\le a_n-b_n$, the descent inequality the proof of Theorem 3.2 is built on.
--
--   **Formalization Note.** Stated for $n\ge2$, as in the paper's proof ("For $n\ge2$ let $a_n=\dots$"); see Lemma 3.1.
-- source:
--   Malitsky, Projected Reflected Gradient Methods for Monotone Variational Inequalities, arXiv:1502.04968v1, p. 5, (3.6), proof of Theorem 3.2

import Mathlib
import Definitions.Def_ProjReflGrad_Weak_Setting

namespace ProjReflGrad.Weak

/-- Inequality (3.6), proof of Theorem 3.2 (Malitsky 2015, p. 5), for `n ≥ 2` and `z ∈ S`:
`‖x_{n+1} - z‖² + λL‖x_{n+1} - y_n‖² + 2λ⟨F(z), x_n - z⟩
  ≤ ‖x_n - z‖² + λL‖x_n - y_{n-1}‖² + 2λ⟨F(z), x_{n-1} - z⟩ - (1 - λL(1 + √2))‖x_n - x_{n-1}‖²`. -/
theorem eq_3_6 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCcl : IsClosed C) (hCcv : Convex ℝ C) (F : H → H) (L lam : ℝ)
    (hC2 : IsMonotoneMap F) (hL : 0 < L) (hC3 : IsLipschitzMap F L)
    (hlam0 : 0 < lam) (hlam1 : lam < (Real.sqrt 2 - 1) / L)
    (x y : ℕ → H) (hrun : IsPRGRun C F lam x y) (z : H) (hz : z ∈ solSet C F) :
    ∀ n : ℕ, 2 ≤ n →
      ‖x (n + 1) - z‖ ^ 2 + lam * L * ‖x (n + 1) - y n‖ ^ 2 + 2 * lam * inner ℝ (F z) (x n - z)
        ≤ ‖x n - z‖ ^ 2 + lam * L * ‖x n - y (n - 1)‖ ^ 2
          + 2 * lam * inner ℝ (F z) (x (n - 1) - z)
          - (1 - lam * L * (1 + Real.sqrt 2)) * ‖x n - x (n - 1)‖ ^ 2 := by sorry

end ProjReflGrad.Weak
