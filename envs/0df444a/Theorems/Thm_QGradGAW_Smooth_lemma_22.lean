-- Prove2me | Theorems.Thm_QGradGAW_Smooth_lemma_22
-- name    : QGradGAW.Smooth.lemma_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:39.457961+00:00
-- url     : https://prove2.me/theorems/0be112a9-cfca-4906-8e52-c0792728f3d0
-- title:
--   Lemma 22, (23), p. 28 — |f′(0)δ − f_(2m)(δ)| ≤ e^{−m/2} ‖f^{(2m+1)}‖∞ |δ|^{2m+1}
-- statement:
--   Let $\delta>0$, let $m\ge1$ be an integer, and let $f$ be $(2m+1)$ times differentiable on the interval $I=[-m\delta,m\delta]$. Let $B$ be a bound for the $(2m+1)$-st derivative on $I$, $|f^{(2m+1)}(\xi)|\le B$ for all $\xi\in I$. Then the degree-$2m$ central difference approximation of $f'(0)\delta$ satisfies
--   $$\Big|f'(0)\,\delta-\sum_{\ell=-m}^{m}a_\ell^{(2m)}\,f(\ell\delta)\Big|\;\le\;e^{-m/2}\,B\,|\delta|^{2m+1}.$$
--
--   Taking $B=\|f^{(2m+1)}\|_\infty=\sup_{\xi\in I}|f^{(2m+1)}(\xi)|$ gives display (23) of the paper. The error therefore decays like $\delta^{2m+1}$, which is what makes higher-degree central differences useful in the gradient algorithm.
--
--   **Formalization Note** "$(2m+1)$ times differentiable on $I$" means that the derivatives of order $0,\dots,2m$ within $I$ are differentiable on $I$; derivatives are taken within $I$. The supremum is replaced by an arbitrary upper bound $B$, which is equivalent and avoids the default value of a supremum over an unbounded set. Since $0$ is interior to $I$, $f'(0)$ is the ordinary derivative. $m\ge1$ because the paper's $\mathbb N$ starts at $1$.
-- source:
--   Gilyén, Arunachalam, Wiebe, Optimizing quantum optimization algorithms via faster quantum gradient computation, arXiv:1711.00465v3, p. 28, Lemma 22, display (23) (restated with proof p. 49)

import Mathlib
import Definitions.Def_QGradGAW_Smooth_Setting

namespace QGradGAW.Smooth

/-- arXiv:1711.00465v3, p. 28 (restated p. 49), Lemma 22, display (23): for `δ > 0`, `m ∈ ℕ₊`
and `f` `(2m+1)`-times differentiable on `I = [−mδ, mδ]` with `|f^{(2m+1)}| ≤ B` on `I`,
`|f′(0)δ − Σ_{ℓ=−m}^{m} a_ℓ^(2m) f(ℓδ)| ≤ e^{−m/2} B |δ|^{2m+1}`. The bound `B` stands for
`‖f^{(2m+1)}‖∞ = sup_{ξ∈I} |f^{(2m+1)}(ξ)|`. -/
theorem lemma_22 (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ) (f : ℝ → ℝ)
    (hf : ∀ j < 2 * m + 1, DifferentiableOn ℝ
      (iteratedDerivWithin j f (Set.Icc (-((m : ℝ) * δ)) ((m : ℝ) * δ)))
      (Set.Icc (-((m : ℝ) * δ)) ((m : ℝ) * δ)))
    (B : ℝ)
    (hB : ∀ ξ ∈ Set.Icc (-((m : ℝ) * δ)) ((m : ℝ) * δ),
      |iteratedDerivWithin (2 * m + 1) f (Set.Icc (-((m : ℝ) * δ)) ((m : ℝ) * δ)) ξ| ≤ B) :
    |deriv f 0 * δ - ∑ ℓ ∈ Finset.Icc (-(m : ℤ)) m, centralCoeff m ℓ * f ((ℓ : ℝ) * δ)| ≤
      Real.exp (-((m : ℝ) / 2)) * B * |δ| ^ (2 * m + 1) := by sorry

end QGradGAW.Smooth
