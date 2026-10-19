-- Prove2me | Theorems.Thm_QAlgorithms_Papers_BansalGupta19_mirrorDescent_regret
-- name    : QAlgorithms.Papers.BansalGupta19.mirrorDescent_regret
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T18:47:47.717526+00:00
-- url     : https://prove2.me/theorems/4b11703c-6e40-4ad2-920b-3a6ee1777395
-- title:
--   Mirror descent regret bound (Bansal–Gupta Theorem 4.2)
-- statement:
--   This is the regret bound of online mirror descent with a constant step size.
--
--   Let $E$ be a finite-dimensional real vector space with an arbitrary norm $\|\cdot\|$, and let $\|g\|_* = \sup_{\|v\| = 1} g(v)$ be the dual norm of a linear functional $g$. Let $K \subseteq E$ be a convex body (closed, convex, with nonempty interior). Let $f_1, \dots, f_T : E \to \mathbb{R}$ be differentiable functions that are convex over $K$. Let $h : E \to \mathbb{R}$ be differentiable and $\alpha_h$-strongly convex with respect to $\|\cdot\|$ for some $\alpha_h > 0$, i.e. $h(y) \ge h(x) + \langle \nabla h(x), y - x\rangle + \frac{\alpha_h}{2}\|y - x\|^2$ for all $x, y$, and let $D_h(y\|x) = h(y) - h(x) - \langle \nabla h(x), y - x\rangle$ be its Bregman divergence. Fix a step size $\eta > 0$ and a starting point $x_0 \in E$. Mirror descent produces $x_1 = \Pi^h_K(x_0)$ and, for $1 \le t < T$, $x_{t+1} = \Pi^h_K(x'_{t+1})$ where $\nabla h(x'_{t+1}) = \nabla h(x_t) - \eta \nabla f_t(x_t)$; here $\Pi^h_K(x') \in K$ minimizes $D_h(\cdot \| x')$ over $K$. Then for every such run and every $x^* \in K$,
--
--   $$
--   \sum_{t=1}^T f_t(x_t) - \sum_{t=1}^T f_t(x^*) \le \frac{D_h(x^*\|x_0)}{\eta} + \frac{\eta}{2\alpha_h}\sum_{t=1}^T \|\nabla f_t(x_t)\|_*^2.
--   $$
--
--   With the Euclidean norm and $h = \frac12\|x\|_2^2$ it recovers the regret bound of projected online gradient descent; with negative entropy on the simplex it gives the Hedge bound.
--
--   **Formalization Note** The source prints the second sum as $\sum_{t=1}^n$; $n$ is a typo for $T$ and is corrected. Gradients are Fréchet derivatives, whose operator norm is the dual norm. The first iterate is the Bregman projection of $x_0$ (equal to $x_0$ when $x_0 \in K$).
-- source:
--   Potential-Function Proofs for First-Order Methods (Bansal, Gupta), arXiv:1712.04581v3, Theorem 4.2, PDF p. 18. https://arxiv.org/abs/1712.04581v3 . PDF SHA-256: 3c0f64d9733bcf1cc4678bd5770e1d0ac7b8a8704373e64157809408f78792b5.

import Definitions.Def_QAlgorithms_Defs_ConvexOpt
set_option autoImplicit false

namespace QAlgorithms.Papers.BansalGupta19

/-- Bansal–Gupta p.18, Theorem 4.2 (cited by Nannicini, Theorem 8.5): the mirror descent regret
bound. Let `K` be a convex body, `f_1, …, f_T` convex functions, `‖·‖` a norm and `h` an
`α_h`-strongly convex function with respect to `‖·‖`. Mirror descent started at `x0` with
constant step size `η` produces `x_1, …, x_T` such that for all `x* ∈ K`
`Σ_{t=1}^T f_t(x_t) − Σ_{t=1}^T f_t(x*) ≤ D_h(x* ‖ x0)/η + η Σ_{t=1}^T ‖∇f_t(x_t)‖_*² / (2α_h)`
(4.40).

Formalization choices.
* The second sum is printed `Σ_{t=1}^n f_t(x*)`; `n` is a typo for `T` (the proof sums the
  amortized inequality over the same `t`), corrected here (trap 30).
* "Convex body" is the p.2 standing assumption: closed, convex, nonempty interior. Convex
  functions are differentiable on the whole space and convex over `K` (p.2); `h : E → ℝ` (p.17).
* `E` is finite-dimensional (the paper's `ℝ^d`).
* The run: `x_1 = Π^h_K(x0)` and, for `1 ≤ t < T`, `x_{t+1} = Π^h_K(x'_{t+1})` with
  `∇h(x'_{t+1}) = ∇h(x_t) − η ∇f_t(x_t)` (4.37); every run satisfying this is covered.
* `α_h > 0` and `η > 0` are the field's implicit conventions (the bound divides by both). -/
theorem mirrorDescent_regret {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Set E) (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    (hKint : (interior K).Nonempty) (T : ℕ) (f : ℕ → E → ℝ)
    (hfdiff : ∀ t ∈ Finset.Icc 1 T, Differentiable ℝ (f t))
    (hfconv : ∀ t ∈ Finset.Icc 1 T, ConvexOn ℝ K (f t)) (h : E → ℝ) (αh : ℝ) (hαh : 0 < αh)
    (hh : IsStronglyConvexWrt h αh) (η : ℝ) (hη : 0 < η) (x0 : E) (x : ℕ → E)
    (hx : IsMirrorDescentRun h K η f x0 T x) (xstar : E) (hxstar : xstar ∈ K) :
    ∑ t ∈ Finset.Icc 1 T, f t (x t) - ∑ t ∈ Finset.Icc 1 T, f t xstar ≤
      bregmanDiv h xstar x0 / η +
        η * (∑ t ∈ Finset.Icc 1 T, ‖fderiv ℝ (f t) (x t)‖ ^ 2) / (2 * αh) := by
  sorry

end QAlgorithms.Papers.BansalGupta19
