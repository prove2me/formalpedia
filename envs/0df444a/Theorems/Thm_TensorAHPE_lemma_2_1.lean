-- Prove2me | Theorems.Thm_TensorAHPE_lemma_2_1
-- name    : TensorAHPE.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:26:05.945304+00:00
-- url     : https://prove2.me/theorems/e27c989f-48a8-4960-aa09-e8b9d877d9ae
-- title:
--   Lemma 2.1: $\|\nabla f(y)-\nabla f_x(y)\|\le\frac{L_d+M}{d!}\|y-x\|^d$
-- statement:
--   Let $d\ge1$, let $f:\mathbb R^n\to\mathbb R$ be $d$ times continuously differentiable with $\|\nabla^d f(x)-\nabla^d f(y)\|\le L_d\|x-y\|$ for all $x,y$, let $M>0$, and let $f_x$ be the regularized Taylor model (2.4). Then for every $x,y\in\mathbb R^n$,
--
--   $$\|\nabla f(y)-\nabla f_x(y)\|\le\frac{L_d+M}{d!}\|y-x\|^d.$$
--
--   The gradient of the model approximates the gradient of $f$ to order $d$; this bound turns an approximate solution of the model subproblem into an approximate proximal step on $F$ (Proposition 3.2).
--
--   **Formalization Note** $\nabla$ is Mathlib's `gradient` on `EuclideanSpace ℝ (Fin n)`.
--
--   Differences from the source:
--   - generalization: f convex (standing assumption (1.1)), L_d a Lipschitz constant → f not assumed convex; no sign condition on L; reason: the bound is a Taylor estimate that uses neither; under the paper's assumptions it is exactly the printed lemma
--   - encoding: ℝⁿ with the Euclidean norm; f d times differentiable with ‖∇ᵈf(x) − ∇ᵈf(y)‖ ≤ L_d‖x − y‖ in the tensor operator norm → EuclideanSpace ℝ (Fin n); ContDiff ℝ d f and the Lipschitz bound on iteratedFDeriv ℝ d f in the multilinear operator norm, with 0 ≤ L; reason: the operator norm of a symmetric tensor over unit vectors equals Mathlib's multilinear norm (flip the sign of one argument); a d-th derivative that is Lipschitz is continuous; a Lipschitz constant is nonnegative
-- source:
--   Jiang, Wang & Zhang, An Optimal High-Order Tensor Method for Convex Optimization, arXiv:1812.06557v3, Lemma 2.1, p.5 (with (2.2) and (2.4), p.5)

import Mathlib
import Definitions.Def_TensorAHPE_model

namespace TensorAHPE

/-- **Lemma 2.1 (gradient of the regularized Taylor model).**
Jiang, Wang & Zhang, *An Optimal High-Order Tensor Method for Convex Optimization*,
arXiv:1812.06557v3, Lemma 2.1, p.5: "For every x, y ∈ ℝⁿ,
‖∇f(y) − ∇f_x(y)‖ ≤ ((L_d + M)/d!)‖y − x‖ᵈ."
Here f satisfies (2.2), p.5 (`∇ᵈf` is `L_d`-Lipschitz) and `f_x` is the model (2.4) with `M > 0`.

**Formalization Note.** `d ≥ 1`; `f` is `ContDiff ℝ d f` with the Lipschitz bound on
`iteratedFDeriv ℝ d f` in the multilinear operator norm; `∇` is Mathlib's `gradient` on
`EuclideanSpace ℝ (Fin n)`. Convexity of `f` (a standing assumption of the paper) is not assumed,
and `L` is not required to be nonnegative. -/
theorem lemma_2_1 {n d : ℕ} (hd : 1 ≤ d) (f : EuclideanSpace ℝ (Fin n) → ℝ) (L M : ℝ)
    (hf : ContDiff ℝ d f)
    (hlip : ∀ x y, ‖iteratedFDeriv ℝ d f x - iteratedFDeriv ℝ d f y‖ ≤ L * ‖x - y‖)
    (hM : 0 < M) (x y : EuclideanSpace ℝ (Fin n)) :
    ‖gradient f y - gradient (model f d M x) y‖ ≤ (L + M) / (d.factorial : ℝ) * ‖y - x‖ ^ d := by sorry

end TensorAHPE
