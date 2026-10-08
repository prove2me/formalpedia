-- Prove2me | Theorems.Thm_TensorNP_SymEigen_stabTensor_symmetric_cubicForm
-- name    : TensorNP.SymEigen.stabTensor_symmetric_cubicForm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:08:18.74625+00:00
-- url     : https://prove2.me/theorems/95a1f8d2-3679-40fe-aa1a-1a2c33ad49aa
-- title:
--   §9, pp. 0:27–0:28 — S_G is symmetric and S_G(z, z, z) = 6 Σ_{i<j, {i,j}∉E} x_i x_j y_ij
-- statement:
--   Let $G=(V,E)$ be a simple graph on $v$ vertices and $\mathcal S=\mathcal S_G\in\mathbb R^{n\times n\times n}$, $n=v+v(v-1)/2$, its tensor from §9. Then:
--
--   1. $\mathcal S$ is symmetric in the sense of (2): $s_{abc}=s_{acb}=s_{bac}=s_{bca}=s_{cab}=s_{cba}$ for all $a,b,c$;
--   2. for every $\mathbf z=(\mathbf x,\mathbf y)\in\mathbb R^v\times\mathbb R^{v(v-1)/2}=\mathbb R^n$,
--   $$\mathcal S(\mathbf z,\mathbf z,\mathbf z)=6\sum_{i<j,\ \{i,j\}\notin E}x_ix_jy_{ij}.$$
--
--   The identity says that $\mathcal S_G$ is the symmetric tensor of Nesterov's cubic, so maximizing the cubic form of $\mathcal S_G$ on the unit sphere is Nesterov's problem up to the factor $6$.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), pp. 0:27–0:28, §9, display S(z, z, z) = 6 Σ x_i x_j y_ij

import Mathlib
import Definitions.Def_TensorNP_SymEigen_Defs
import Definitions.Def_TensorNP_SymEigen_StabTensor

namespace TensorNP.SymEigen

theorem stabTensor_symmetric_cubicForm {v : ℕ} (G : SimpleGraph (Fin v)) :
    IsSymmetric (stabTensor G) ∧
      ∀ z : Idx v → ℝ, cubicForm (stabTensor G) z =
        6 * nesterovForm G (fun i => z (Sum.inl i)) (fun p => z (Sum.inr p)) := by sorry

end TensorNP.SymEigen
