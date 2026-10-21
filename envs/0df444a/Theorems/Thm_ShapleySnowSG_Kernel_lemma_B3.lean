-- Prove2me | Theorems.Thm_ShapleySnowSG_Kernel_lemma_B3
-- name    : ShapleySnowSG.Kernel.lemma_B3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:58:44.03926+00:00
-- url     : https://prove2.me/theorems/db293887-6a42-41a8-ab52-f6d25e80177e
-- title:
--   Lemma B3, p. 29 — a square matrix of corank one has co(M) = α x ᵗy with α ≠ 0, x, y spanning the left and right kernels
-- statement:
--   Let $M$ be a real square matrix of size $a\ge1$ and rank $a-1$, and let $x,y\in\mathbb R^a$ be such that $\mathrm{Ker}({}^tM)=\langle x\rangle$ and $\mathrm{Ker}(M)=\langle y\rangle$. Then there is a constant $\alpha\neq0$ such that
--   $$\mathrm{co}(M)=\alpha\,x\,{}^ty .$$
--
--   This rank-one description of the cofactor matrix is the step that identifies a kernel's strategies with the kernel vectors of $\dot G-v\dot U$.
--
--   **Formalization Note** $\langle x\rangle=\{tx:t\in\mathbb R\}$ is the span `ℝ ∙ x`; $x\,{}^ty$ is `vecMulVec x y`.
-- source:
--   Attia & Oliu-Barton, Shapley–Snow kernels, multiparameter eigenvalue problems and stochastic games, arXiv:1810.08798v2, p. 29, Lemma B3

import Mathlib
import Definitions.Def_ShapleySnowSG_Kernel_MatrixGame

namespace ShapleySnowSG.Kernel

open Matrix

/-- Lemma B3, p. 29: if `M` is square of size `a ≥ 1` and rank `a − 1`, with
`Ker(ᵗM) = ⟨x⟩` and `Ker(M) = ⟨y⟩`, then `co(M) = α x ᵗy` for some `α ≠ 0`. -/
theorem lemma_B3 {a : ℕ} (ha : 0 < a) (M : Matrix (Fin a) (Fin a) ℝ) (hrank : M.rank = a - 1)
    (x y : Fin a → ℝ) (hx : LinearMap.ker Mᵀ.mulVecLin = ℝ ∙ x)
    (hy : LinearMap.ker M.mulVecLin = ℝ ∙ y) :
    ∃ α : ℝ, α ≠ 0 ∧ co M = α • vecMulVec x y := by sorry

end ShapleySnowSG.Kernel
