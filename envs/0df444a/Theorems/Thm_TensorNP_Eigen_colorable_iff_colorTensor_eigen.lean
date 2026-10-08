-- Prove2me | Theorems.Thm_TensorNP_Eigen_colorable_iff_colorTensor_eigen
-- name    : TensorNP.Eigen.colorable_iff_colorTensor_eigen
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:08:11.354488+00:00
-- url     : https://prove2.me/theorems/bade250f-e016-46df-b106-66cfddc2148b
-- title:
--   Proof of Theorem 1.3 — $G$ is 3-colorable iff $0$ is a real eigenvalue of $T_G$
-- statement:
--   Let $G$ be a simple graph on $v$ vertices and $N=8v+2$. Let $T_G\in\mathbb Q^{N\times N\times N}$ be the integral tensor of the reduction: the color encoding $C_G$ (Definition 2.9, $4v$ quadratics in $2v+1$ complex unknowns) is turned by Lemma 2.7 into $8v$ real quadratics in $4v+2$ unknowns, then by Lemma 2.8 with $r=s=N$ into a square system $\mathbf x^\top B_k\mathbf x=0$ ($k=1,\dots,N$), and $T_G=[\![a_{ijk}]\!]$ with $a_{ijk}=(B_k)_{ij}$. Then
--
--   $$G\text{ is 3-colorable}\iff \exists\,\mathbf 0\ne\mathbf x\in\mathbb R^N:\ \sum_{i,j=1}^{N}a_{ijk}x_ix_j=0\quad(k=1,\dots,N),$$
--
--   i.e. iff $0$ is a real eigenvalue of $T_G$.
--
--   This is the correctness of the paper's reduction; together with the polynomial size of $T_G$ it gives Theorem 1.3.
--
--   **Formalization Note** The size $N=8v+2$ is one admissible choice for Lemma 2.8 ($r\ge 8v+1$, $s\ge 4v+2$) valid also for $v=0$; Example 1.4 uses a different encoding count.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:20, proof of Theorem 1.3 (with p. 0:17, proof of Theorem 3.8, and pp. 0:7–0:8, Example 1.4)

import Mathlib
import Definitions.Def_TensorNP_Eigen_Construction

namespace TensorNP.Eigen

/-- Proof of Theorem 1.3 (with the proof of Theorem 3.8 and Example 1.4): a simple graph `G` on
`v` vertices is 3-colorable if and only if `0` is a real eigenvalue of the integral tensor
`T_G ∈ ℚ^{N×N×N}`, `N = 8v + 2`, built from `C_G` by Lemmas 2.7 and 2.8. -/
theorem colorable_iff_colorTensor_eigen {v : ℕ} (G : SimpleGraph (Fin v)) :
    G.Colorable 3 ↔ IsEigenvalue (castTensor ℝ (colorTensor G)) 0 := by sorry

end TensorNP.Eigen
