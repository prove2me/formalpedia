-- Prove2me | Theorems.Thm_TensorNP_Eigen_lemma_2_10
-- name    : TensorNP.Eigen.lemma_2_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:08:22.365392+00:00
-- url     : https://prove2.me/theorems/2ce1b54f-5b64-4cd5-bb99-9f8f1b9089a6
-- title:
--   Lemma 2.10 — $C_G$ has a nonzero complex solution iff $G$ is 3-colorable
-- statement:
--   Let $G=(V,E)$ be a simple graph with vertices $1,\dots,v$, and let $C_G$ be its color encoding (Definition 2.9): the $4v$ quadratic polynomials
--
--   $$x_iy_i-z^2,\quad y_iz-x_i^2,\quad x_iz-y_i^2,\quad \sum_{j:\{i,j\}\in E}(x_i^2+x_ix_j+x_j^2),\qquad i=1,\dots,v,$$
--
--   in the $2v+1$ unknowns $x_1,\dots,x_v,y_1,\dots,y_v,z$. Then the polynomials of $C_G$ have a common zero $\mathbf 0\ne(x_1,\dots,x_v,y_1,\dots,y_v,z)\in\mathbb C^{2v+1}$ if and only if $G$ is 3-colorable.
--
--   This is the algebraic heart of the reduction: a proper 3-coloring corresponds to assigning cube roots of unity to the vertices.
--
--   **Formalization Note** Each polynomial is a rational matrix $M$ evaluated as $\mathbf w^\top M\mathbf w$ after casting to $\mathbb C$. For $v=0$ the system has no equations and the single unknown $z$, and both sides hold.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:14, Lemma 2.10 (proof pp. 0:14–0:15)

import Mathlib
import Definitions.Def_TensorNP_Eigen_Construction

namespace TensorNP.Eigen

open Matrix

/-- Lemma 2.10: the color encoding `C_G` of a simple graph `G` on `v` vertices has a nonzero
complex solution `w ∈ ℂ^{2v+1}` if and only if `G` is 3-colorable. -/
theorem lemma_2_10 {v : ℕ} (G : SimpleGraph (Fin v)) :
    QuadSolvable (castMatrices ℂ (colorEncoding G)) ↔ G.Colorable 3 := by sorry

end TensorNP.Eigen
