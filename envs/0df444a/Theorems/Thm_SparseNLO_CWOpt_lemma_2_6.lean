-- Prove2me | Theorems.Thm_SparseNLO_CWOpt_lemma_2_6
-- name    : SparseNLO.CWOpt.lemma_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T15:12:31.839626+00:00
-- url     : https://prove2.me/theorems/51aba99e-8998-4b28-8ed0-e19f31a173ac
-- title:
--   Lemma 2.6 (Local Descent Lemma) — f(x + d) ≤ f(x) + ∇f(x)ᵀd + (L₂(f)/2)‖d‖² for d with at most two nonzero components
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be continuously differentiable and bounded below, with $L(f)$-Lipschitz gradient (Assumption 2), and let $L_2$ be a constant satisfying the local Lipschitz condition (2.15): for all $i\neq j$, all $x$ and all $d$ supported in $\{i,j\}$, $\|\nabla_{i,j}f(x)-\nabla_{i,j}f(x+d)\|\le L_2\|d\|$.
--
--   Then for all indices $i\neq j$, every $x\in\mathbb R^n$ and every $d\in\mathbb R^n$ whose nonzero components lie in $\{i,j\}$,
--   $$f(x+d)\le f(x)+\nabla f(x)^Td+\frac{L_2}{2}\|d\|^2 .$$
--
--   This is the local version of the classical descent lemma: along directions with at most two nonzero entries the quadratic upper bound holds with the local constant $L_2(f)$, which may be much smaller than the global Lipschitz constant $L(f)$ (Example 2.1). It is the quantitative tool behind Theorem 2.4.
--
--   **Formalization Note** "Any vector $d$ with at most two nonzero components" is formalized as "$d$ supported in some $\{i,j\}$ with $i\neq j$"; for $n\ge2$ every vector with at most two nonzero components is of this form. $L_2$ is any constant satisfying (2.15), in particular the paper's $L_2(f)$. Assumption 2 (with some constant $L_f$) and Assumption 1 are kept as on the page, although (2.15) is the hypothesis the inequality rests on. The inner product is the Euclidean one.
-- source:
--   Beck, Eldar, Sparsity Constrained Nonlinear Optimization: Optimality Conditions and Algorithms, SIAM J. Optim. (2013), doi:10.1137/120869778 (source: arXiv:1203.4580v1), p. 12, Lemma 2.6 (with (2.15), p. 11)

import Mathlib
import Definitions.Def_SparseNLO_CWOpt_Setting

open scoped RealInnerProductSpace

namespace SparseNLO.CWOpt

/-- Lemma 2.6 (Local Descent Lemma, p. 12): under Assumption 2, with `L2` a constant satisfying
(2.15), `f(x + d) ≤ f(x) + ∇f(x)ᵀd + (L2/2)‖d‖²` for every `d` with at most two nonzero
components, i.e. supported in some `{i, j}` with `i ≠ j`. -/
theorem lemma_2_6 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (hbdd : ∃ γ : ℝ, ∀ x, γ ≤ f x)
    (Lf : NNReal) (hLf : LipschitzWith Lf (gradient f))
    (L2 : ℝ) (hL2 : LocalLipschitz f L2)
    (i j : Fin n) (hij : i ≠ j) (x d : EuclideanSpace ℝ (Fin n))
    (hd : ∀ k : Fin n, k ≠ i → k ≠ j → d k = 0) :
    f (x + d) ≤ f x + ⟪gradient f x, d⟫ + L2 / 2 * ‖d‖ ^ 2 := by sorry

end SparseNLO.CWOpt
