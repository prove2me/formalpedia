-- Prove2me | Theorems.Thm_SphereSOS_Rate_theorem_2
-- name    : SphereSOS.Rate.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:19:55.298279+00:00
-- url     : https://prove2.me/theorems/06df5fc4-3fdc-418f-ab8c-5e92dd59d9c4
-- title:
--   Theorem 2, p. 3 — if $0\preceq F\preceq I$ on $S^{d-1}$, $F+C'_n(d/\ell)^2I$ is $\ell$-sos on $S^{d-1}$ for all $\ell\ge C_nd$
-- statement:
--   For every $n\ge0$ there are constants $C_n$ and $C'_n$, depending only on $n$, with the following property. Let $d,k,\ell\ge0$ and let $F(x_1,\dots,x_d)$ be a $k\times k$ matrix polynomial, homogeneous of degree $2n$, with $n\le d$, such that $F(x)$ is symmetric for every $x\in\mathbb R^d$ and
--   $$0\preceq F(x)\preceq I\qquad\text{for all }x\in S^{d-1}.$$
--   If $\ell\ge C_nd$, then
--   $$F+C'_n\Big(\frac d\ell\Big)^2I\quad\text{is }\ell\text{-sos on }S^{d-1}.$$
--
--   This is the main theorem: the sum-of-squares hierarchy on the sphere converges at the rate $(d/\ell)^2$ once $\ell\ge C_nd$, uniformly in the size $k$ of the matrices. The scalar case ($k=1$) gives Theorem 1.
--
--   **Formalization Note** The constants are chosen before $d$, $k$, $\ell$ and $F$, so they are independent of the dimension and of the matrix size. $\preceq$ is the positive semidefinite order, imposed on the sphere only. No assumption $d\ge2$ is added: for $d\le1$ the statement is elementary and true. If $C_n\le0$, $\ell=0$ is admitted and Lean reads $(d/0)^2$ as $0$; the conclusion then claims $F$ is $0$-sos, which fails in general, so this gives a prover nothing.
-- source:
--   Fang, Fawzi, The sum-of-squares hierarchy on the sphere, and applications in quantum information theory, arXiv:1908.05155v1, p. 3, Theorem 2

import Mathlib
import Definitions.Def_SphereSOS_Rate_Setting

namespace SphereSOS.Rate

theorem theorem_2 :
    ∀ n : ℕ, ∃ C C' : ℝ, ∀ (d k ℓ : ℕ)
      (F : Matrix (Fin k) (Fin k) (MvPolynomial (Fin d) ℝ)),
      n ≤ d →
      (∀ a b, (F a b).IsHomogeneous (2 * n)) →
      (∀ x, (evalM x F).IsSymm) →
      (∀ x ∈ sphere d,
        (evalM x F).PosSemidef ∧ (1 - evalM x F).PosSemidef) →
      C * (d : ℝ) ≤ (ℓ : ℝ) →
      IsSosOnSphere ℓ
        (F + (C' * ((d : ℝ) / (ℓ : ℝ)) ^ 2) •
          (1 : Matrix (Fin k) (Fin k) (MvPolynomial (Fin d) ℝ))) := by sorry

end SphereSOS.Rate
