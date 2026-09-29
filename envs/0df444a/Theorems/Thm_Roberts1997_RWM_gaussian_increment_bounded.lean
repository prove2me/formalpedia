-- Prove2me | Theorems.Thm_Roberts1997_RWM_gaussian_increment_bounded
-- name    : Roberts1997.RWM.gaussian_increment_bounded
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:48:26.523771+00:00
-- url     : https://prove2.me/theorems/4281b1a7-8d13-4861-b7ea-24dd9772e658
-- title:
--   Lemma 2.5 — limsup over n of sup over x₁ of n|𝔼[V(Y₁) − V(x₁)]| is finite for V ∈ C_c^∞
-- statement:
--   Let $V\in C_c^\infty(\mathbb R)$ and $l>0$, and let $Y_1\sim N(x_1,\sigma_n^2)$ with $\sigma_n^2=l^2/(n-1)$. Then
--
--   $$ \limsup_{n\to\infty}\ \sup_{x_1\in\mathbb R}\ n\,\big|\mathbb E[V(Y_1)-V(x_1)]\big|<\infty ; $$
--
--   that is, there is a constant $C$ such that for all sufficiently large $n$ and all $x_1\in\mathbb R$, $n\,|\mathbb E[V(Y_1)-V(x_1)]|\le C$.
--
--   The bound controls the first-coordinate increment of the speeded-up chain uniformly in the starting point.
--
--   **Formalization Note** "$\limsup\sup<\infty$" is stated as eventual uniform boundedness, which is equivalent and avoids a real supremum or limsup. $C_c^\infty$ is `ContDiff ℝ ∞ V` (smooth) with `HasCompactSupport V`. $V$ is bounded and continuous, so the expectation is a genuine integral.
-- source:
--   Roberts, Gelman, Gilks, Weak convergence and optimal scaling of random walk Metropolis algorithms, Ann. Appl. Probab. 7(1), 1997, pp. 115–116, Lemma 2.5

import Definitions.Def_Roberts1997_RWM_Target

open MeasureTheory ProbabilityTheory Filter
open scoped ContDiff

namespace Roberts1997.RWM

/-- Lemma 2.5 (pp. 115–116). For `V ∈ C_c^∞`,
`limsup_{n→∞} sup_{x₁ ∈ ℝ} n |𝔼[V(Y₁) - V(x₁)]| < ∞` with `Y₁ ~ N(x₁, σ_n²)`; stated as
eventual uniform boundedness. -/
theorem gaussian_increment_bounded (V : ℝ → ℝ) (hV : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport V) (l : ℝ) (hl : 0 < l) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ x₁ : ℝ,
      (n : ℝ) * |∫ y, (V y - V x₁) ∂(gaussianReal x₁ (sigmaSq n l).toNNReal)| ≤ C := by sorry

end Roberts1997.RWM
