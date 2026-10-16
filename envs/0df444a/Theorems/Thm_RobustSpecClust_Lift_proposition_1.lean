-- Prove2me | Theorems.Thm_RobustSpecClust_Lift_proposition_1
-- name    : RobustSpecClust.Lift.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:43:31.480613+00:00
-- url     : https://prove2.me/theorems/a3e0a226-e94f-4f02-8b8e-69699b3a9d94
-- title:
--   Proposition 1: binary PSD lifting and robust cluster assignment are equivalent up to rotation
-- statement:
--   Consider formulations (3) and (4) with $N$ observations, at most $r$ clusters, any real similarity matrix $K$, and any real penalty $\gamma$. If $X^*$ globally maximizes the lifted objective over binary positive semidefinite matrices of rank at most $r$, then there are a factor $G\in\mathbb R^{N\times r}$ and an orthogonal matrix $O\in\mathbb R^{r\times r}$ such that $Z^*=GO$ is a globally optimal feasible binary assignment matrix in (3), and
--
--   $$
--   X^*=GG^\top,\qquad F_3(Z^*)=F_4(X^*).
--   $$
--
--   Feasibility of $Z^*$ includes the zero-row option for outliers. The statement establishes that the lifted optimum can be recovered as a cluster assignment after a rotation, with no loss of objective value.
--
--   **Formalization Note** Proposition 1 uses only the algebra of (3) and (4), so $K$ and $\gamma$ are arbitrary real data. The orthogonal factor has exactly $r$ columns, including when $r=0$.
-- source:
--   arXiv:1912.07546v3, Proposition 1, p. 9, formulations (3) and (4) on p. 8; proof in Appendix B, pp. 37–38

import Mathlib
import Definitions.Def_RobustSpecClust_Lift_Setting

namespace RobustSpecClust.Lift

theorem proposition_1 {N r : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) (γ : ℝ)
    (X : Matrix (Fin N) (Fin N) ℝ) (hX : IsOpt4 K γ r X) :
    ∃ G : Matrix (Fin N) (Fin r) ℝ, X = G * G.transpose ∧
      ∃ O ∈ Matrix.orthogonalGroup (Fin r) ℝ,
        IsOpt3 K γ (G * O) ∧ obj3 K γ (G * O) = obj4 K γ X := by sorry

end RobustSpecClust.Lift
