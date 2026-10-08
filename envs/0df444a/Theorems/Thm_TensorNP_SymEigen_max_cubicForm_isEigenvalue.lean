-- Prove2me | Theorems.Thm_TensorNP_SymEigen_max_cubicForm_isEigenvalue
-- name    : TensorNP.SymEigen.max_cubicForm_isEigenvalue
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:08:33.757709+00:00
-- url     : https://prove2.me/theorems/1c1c1f55-5be9-4283-9d0c-7ee43a2300db
-- title:
--   §9, p. 0:28 — the maximum of S_G(z, z, z) on ‖z‖₂ = 1 is attained and is an ℓ²-eigenvalue of S_G
-- statement:
--   Let $G$ be a simple graph on $v\ge1$ vertices and $\mathcal S=\mathcal S_G$ its tensor from §9. Then
--   $$\lambda=\max_{\|\mathbf z\|_2=1}\mathcal S(\mathbf z,\mathbf z,\mathbf z)$$
--   exists, and $\lambda$ is a unit $\ell^2$-eigenvalue of $\mathcal S$: there is $\mathbf z$ with $\|\mathbf z\|_2=1$ and $\sum_{a,b}s_{abc}z_az_b=\lambda z_c$ for every $c$.
--
--   In the paper this is the remark that the maximum of the cubic form on the sphere is a stationary value of the constrained problem, hence an eigenvalue. It is the half of the reduction that turns an optimization value into an eigenvalue query.
--
--   **Formalization Note** "$\ell^2$-eigenvalue" is read with a unit eigenvector (see the definitions item). The hypothesis $v\ge1$ makes the sphere nonempty.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:28, §9, sentence before Theorem 9.3 ("Since λ = max_{‖z‖₂=1} S(z, z, z) …, it is an ℓ²-eigenvalue of S")

import Mathlib
import Definitions.Def_TensorNP_SymEigen_Defs
import Definitions.Def_TensorNP_SymEigen_StabTensor

namespace TensorNP.SymEigen

theorem max_cubicForm_isEigenvalue {v : ℕ} (hv : 0 < v) (G : SimpleGraph (Fin v)) :
    ∃ lam : ℝ,
      IsGreatest {t : ℝ | ∃ z : Idx v → ℝ, l2norm z = 1 ∧ t = cubicForm (stabTensor G) z} lam ∧
        IsUnitL2Eigenvalue (stabTensor G) lam := by sorry

end TensorNP.SymEigen
