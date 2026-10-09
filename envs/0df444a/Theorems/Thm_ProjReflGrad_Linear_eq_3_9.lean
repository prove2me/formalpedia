-- Prove2me | Theorems.Thm_ProjReflGrad_Linear_eq_3_9
-- name    : ProjReflGrad.Linear.eq_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:14:10.523982+00:00
-- url     : https://prove2.me/theorems/7cccc04e-9796-46d6-b8f6-2ff5caf72382
-- title:
--   (3.9), proof of Theorem 3.3, p. 7 — the two-step recursion with β = max{λL/(1 − √2λL), 1/2}, n ≥ 2
-- statement:
--   Let $H$ be a real Hilbert space, $C\subseteq H$ closed and convex, $F:H\to H$ strongly monotone with modulus $m>0$ and $L$-Lipschitz with $L>0$, and $0<\lambda<(\sqrt2-1)/L$. Let $(x_n),(y_n)$ be a run of Algorithm 3.1 and $z$ a solution of (1.1). Put
--   $$\beta=\max\Big\{\frac{\lambda L}{1-\sqrt2\lambda L},\ \frac12\Big\}.$$
--   Then for every $m_1\in(0,m]$ and every $n\ge2$,
--   $$\|x_{n+1}-z\|^2+(1-\sqrt2\lambda L)\|x_{n+1}-y_n\|^2+4\lambda\langle F(z),x_n-z\rangle\ \le\ (1-4\lambda m_1)\|x_n-z\|^2+2\lambda m_1\|x_{n-1}-z\|^2+\beta\Big((1-\sqrt2\lambda L)\|x_n-y_{n-1}\|^2+4\lambda\langle F(z),x_{n-1}-z\rangle\Big).\qquad(3.9)$$
--
--   With $a_n=\|x_n-z\|^2$, $b_n=(1-\sqrt2\lambda L)\|x_n-y_{n-1}\|^2+4\lambda\langle F(z),x_{n-1}-z\rangle$ and $\alpha=2\lambda m_1$ this is the recursion $a_{n+1}+b_{n+1}\le(1-2\alpha)a_n+\alpha a_{n-1}+\beta b_n$ of Lemma 2.8, from which the linear rate follows.
--
--   **Formalization Note.** The step range gives $1-\sqrt2\lambda L>0$, so the division in $\beta$ is a genuine real quotient. The range $n\ge2$ is needed because the proof uses (3.4) and $\langle F(z),x_{n-1}-z\rangle\ge0$, both requiring $x_{n-1}\in C$, while $x_0$ may lie outside $C$. The page displays a chain of two inequalities; the statement is its outer inequality (first left side $\le$ last right side). Existence of a solution is not assumed separately: $z$ is given.
-- source:
--   Malitsky, Projected Reflected Gradient Methods for Monotone Variational Inequalities, arXiv:1502.04968v1, p. 7, (3.9), proof of Theorem 3.3

import Mathlib
import Definitions.Def_ProjReflGrad_Linear_Setting

namespace ProjReflGrad.Linear

/-- Inequality (3.9), proof of Theorem 3.3 (Malitsky 2015, p. 7), for `n ≥ 2`: under (C2*) with
modulus `m > 0`, (C3) with `L > 0` and `0 < λ < (√2 - 1)/L`, along a run of Algorithm 3.1, for the
solution `z` and every `m₁ ∈ (0, m]`, with `β = max{λL/(1 - √2λL), 1/2}`,
`‖x_{n+1} - z‖² + (1 - √2λL)‖x_{n+1} - y_n‖² + 4λ⟨F(z), x_n - z⟩
  ≤ (1 - 4λm₁)‖x_n - z‖² + 2λm₁‖x_{n-1} - z‖²
    + β((1 - √2λL)‖x_n - y_{n-1}‖² + 4λ⟨F(z), x_{n-1} - z⟩)`. -/
theorem eq_3_9 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCcl : IsClosed C) (hCcv : Convex ℝ C) (F : H → H) (L lam m : ℝ)
    (hm : 0 < m) (hC2s : IsStronglyMonotoneMap F m) (hL : 0 < L) (hC3 : ProjReflGrad.Weak.IsLipschitzMap F L)
    (hlam0 : 0 < lam) (hlam1 : lam < (Real.sqrt 2 - 1) / L)
    (x y : ℕ → H) (hrun : ProjReflGrad.Weak.IsPRGRun C F lam x y) (z : H) (hz : z ∈ ProjReflGrad.Weak.solSet C F) :
    ∀ m1 : ℝ, 0 < m1 → m1 ≤ m → ∀ n : ℕ, 2 ≤ n →
      ‖x (n + 1) - z‖ ^ 2 + (1 - Real.sqrt 2 * lam * L) * ‖x (n + 1) - y n‖ ^ 2
          + 4 * lam * inner ℝ (F z) (x n - z) ≤
        (1 - 4 * lam * m1) * ‖x n - z‖ ^ 2 + 2 * lam * m1 * ‖x (n - 1) - z‖ ^ 2
          + max (lam * L / (1 - Real.sqrt 2 * lam * L)) (1 / 2)
            * ((1 - Real.sqrt 2 * lam * L) * ‖x n - y (n - 1)‖ ^ 2
              + 4 * lam * inner ℝ (F z) (x (n - 1) - z)) := by sorry

end ProjReflGrad.Linear
