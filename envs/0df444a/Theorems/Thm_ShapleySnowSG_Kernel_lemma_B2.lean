-- Prove2me | Theorems.Thm_ShapleySnowSG_Kernel_lemma_B2
-- name    : ShapleySnowSG.Kernel.lemma_B2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:58:40.243968+00:00
-- url     : https://prove2.me/theorems/639f1f35-b49c-464c-bbed-9f4d1990740f
-- title:
--   Lemma B2, p. 29 — Ġ + wU̇ is a Shapley–Snow kernel of the translated game G + wU
-- statement:
--   Let $G$ be a real $I\times J$ matrix game ($I,J$ finite, nonempty) and $\dot G$ a Shapley–Snow kernel of $G$, with rows $\dot I$ and columns $\dot J$. Then for every $w\in\mathbb R$ the sub-matrix
--   $$\dot G+w\dot U$$
--   on the same rows and columns is a Shapley–Snow kernel of the translated game $G+wU$, where $U$ is the matrix of ones.
--
--   It is used to pass from a kernel of the local game $\mathcal G^k(\lambda,v_\lambda)$ to a kernel of the normalised game $\mathcal G^k(\lambda,v_\lambda)-v^k_\lambda U$.
-- source:
--   Attia & Oliu-Barton, Shapley–Snow kernels, multiparameter eigenvalue problems and stochastic games, arXiv:1810.08798v2, p. 29, Lemma B2

import Mathlib
import Definitions.Def_ShapleySnowSG_Kernel_MatrixGame

namespace ShapleySnowSG.Kernel

open Matrix

/-- Lemma B2, p. 29: if `Ġ` is a Shapley–Snow kernel of `G`, then `Ġ + wU̇` is a Shapley–Snow
kernel of the translated game `G + wU`, for any `w ∈ ℝ`. -/
theorem lemma_B2 {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (G : Matrix ι κ ℝ) (s : ℕ) (r : Fin s ↪ ι) (c : Fin s ↪ κ) (hK : IsSSK G s r c) (w : ℝ) :
    IsSSK (G + w • onesMat ι κ) s r c := by sorry

end ShapleySnowSG.Kernel
