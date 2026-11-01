-- Prove2me | Theorems.Thm_StochCoordProx_lemma_1_descent_along_U
-- name    : StochCoordProx.lemma_1_descent_along_U
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T11:33:17.060201+00:00
-- url     : https://prove2.me/theorems/4a9d4704-3995-423f-94c0-8e05cf0cd625
-- title:
--   Lemma 1 — descent lemma along $U$
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be differentiable, let $U\in\mathbb R^{n\times p}$, and suppose $f$ is $L_U$ smooth along $U$, i.e. $\|U^T(\nabla f(x+Uh)-\nabla f(x))\|\le L_U\|h\|$ for all $x\in\mathbb R^n$, $h\in\mathbb R^p$. Then
--
--   $$
--   |f(x+Uh)-f(x)-\langle U^T\nabla f(x),h\rangle|\le\frac{L_U}{2}\|h\|^2\qquad\forall x\in\mathbb R^n,\ h\in\mathbb R^p .
--   $$
--
--   This quadratic bound along the subspace is the basic estimate behind the descent property of SCPG (Lemma 4).
--
--   Differences from the source:
--   - generalization: Assumption 1 [A.1] for every U in the family 𝒰 → one matrix U with a constant L_U satisfying (2); reason: the conclusion concerns one U; A.1 supplies this for every U ∈ 𝒰
--   - generalization: f is L_U smooth along U (A.1) → f differentiable on ℝⁿ and (2) for U with constant L_U; reason: the paper defines the term by (2) and uses nothing else; any smooth f satisfying (2) is an instance
--   - encoding: vectors of ℝⁿ, ℝᵖ and matrices U ∈ ℝ^{n×p} → EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin p), U acting through Matrix.toEuclideanLin; reason: Lean convention; the Euclidean norm and inner product of the paper, same instances
--   - generalization: the set 𝒰 bounded (standing assumption, p.4); 𝓛_F(x₀) bounded (standing assumption, p.7: "Throughout the paper, we also assume boundedness of the level set") → not assumed; reason: the proof does not use them; they serve only to make H_{F,max} finite, which this statement does not involve; every instance satisfying them is covered
-- source:
--   Necoara & Chorobura, Efficiency of stochastic coordinate proximal gradient methods on nonseparable composite optimization, arXiv:2104.13370v3, Lemma 1, display (3), p.5

import Mathlib
import Definitions.Def_StochCoordProx_IsSmoothAlong

open Matrix
open scoped InnerProductSpace

namespace StochCoordProx

/-- **Lemma 1 (descent lemma along `U`).** If `f : ℝⁿ → ℝ` is differentiable and `L_U` smooth
along `U ∈ ℝ^{n×p}` (display (2)), then for all `x ∈ ℝⁿ` and `h ∈ ℝᵖ`
`|f(x + U h) − f(x) − ⟨Uᵀ∇f(x), h⟩| ≤ (L_U/2) ‖h‖²`  (3).

Necoara & Chorobura, arXiv:2104.13370v3, Lemma 1, display (3), p.5.

**Formalization Note.** Stated for one matrix `U` with its constant `L_U` ("Assumption 1 [A1]"
restricted to that `U`). Euclidean spaces; `U` acts as `Matrix.toEuclideanLin U`. -/
theorem lemma_1_descent_along_U {n p : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Matrix (Fin n) (Fin p) ℝ) (LU : ℝ) (hf : Differentiable ℝ f)
    (hL : IsSmoothAlong f U LU) (x : EuclideanSpace ℝ (Fin n)) (h : EuclideanSpace ℝ (Fin p)) :
    |f (x + Matrix.toEuclideanLin U h) - f x - ⟪Matrix.toEuclideanLin Uᵀ (gradient f x), h⟫_ℝ| ≤
      LU / 2 * ‖h‖ ^ 2 := by sorry

end StochCoordProx
