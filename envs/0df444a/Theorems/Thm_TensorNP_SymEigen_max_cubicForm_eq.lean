-- Prove2me | Theorems.Thm_TensorNP_SymEigen_max_cubicForm_eq
-- name    : TensorNP.SymEigen.max_cubicForm_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:08:29.247092+00:00
-- url     : https://prove2.me/theorems/3a4753c8-229c-42c4-a6cb-b4e6237af3c0
-- title:
--   §9, p. 0:28 — max_{‖z‖₂=1} S_G(z, z, z) = 2√((2/3)(1 − 1/α(G)))
-- statement:
--   Let $G$ be a simple graph on $v\ge1$ vertices with stability number $\alpha(G)$, and $\mathcal S=\mathcal S_G$ its tensor from §9. Then the maximum of the cubic form of $\mathcal S$ on the unit sphere of $\mathbb R^n$ is attained and equals
--   $$\max_{\|\mathbf z\|_2=1}\mathcal S(\mathbf z,\mathbf z,\mathbf z)=2\sqrt{\frac23\left(1-\frac1{\alpha(G)}\right)}=\lambda_{\alpha(G)} .$$
--
--   This is the paper's consequence of Nesterov's theorem: the largest value of the cubic form of $\mathcal S_G$ determines $\alpha(G)$, since $l\mapsto\lambda_l$ is strictly increasing on $l\ge1$.
--
--   **Formalization Note** The maximum is stated as the greatest element of the set of values $\{\mathcal S(\mathbf z,\mathbf z,\mathbf z):\|\mathbf z\|_2=1\}$, so attainment is part of the claim.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:28, §9, display "Moreover, Nesterov's Theorem implies λ = 2√((2/3)(1 − 1/α(G)))"

import Mathlib
import Definitions.Def_TensorNP_SymEigen_Defs
import Definitions.Def_TensorNP_SymEigen_StabTensor

namespace TensorNP.SymEigen

theorem max_cubicForm_eq {v : ℕ} (hv : 0 < v) (G : SimpleGraph (Fin v)) :
    IsGreatest {t : ℝ | ∃ z : Idx v → ℝ, l2norm z = 1 ∧ t = cubicForm (stabTensor G) z}
      (lambdaL G.indepNum) := by sorry

end TensorNP.SymEigen
