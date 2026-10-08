-- Prove2me | Theorems.Thm_ProbMetricStab_Portfolio_nonsingular_quadratic_growth
-- name    : ProbMetricStab.Portfolio.nonsingular_quadratic_growth
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T23:05:07.076809+00:00
-- url     : https://prove2.me/theorems/0456101d-2a35-44cf-b7a6-d15cac966988
-- title:
--   Proof of Theorem 5.2, p. 25 — Γ nonsingular ⇒ S(α, Γ) = {x_*} and ¼cα(α − 1)‖x − x_*‖² ≤ r_{α,Γ}(x) − v(α, Γ)
-- statement:
--   Let $\Gamma$ be a nonsingular Borel probability measure on the unit sphere $\Sigma^s\subset\mathbb R^s$, and let $c>0$ be a constant (depending only on $s$ and $\Gamma$) with $c\|y\|^2\le\int_{\Sigma^s}|\langle y,\xi\rangle|^2\Gamma(d\xi)$ for all $y\in\mathbb R^s$. Then for every stability index $\alpha\in(1,2)$ problem (22), $\min\{r_{\alpha,\Gamma}(x):x\in X\}$, has a unique solution $x_*$, i.e. $S(\alpha,\Gamma)=\{x_*\}$, and
--   $$\tfrac14\,c\,\alpha(\alpha-1)\|x-x_*\|^2\le r_{\alpha,\Gamma}(x)-v(\alpha,\Gamma)\qquad\text{for each }x\in X.$$
--
--   This quadratic growth of the risk around its unique minimizer is what makes the stability modulus $\Psi$ of Theorem 5.2 of order $\eta^{1/2}$.
--
--   **Formalization Note** The constant $c$ is the constant of the norm bound $c\|y\|^2\le\int_{\Sigma^s}|\langle y,\xi\rangle|^2\Gamma(d\xi)$ from the preceding sentence of the proof (the milestone `nonsingular_norm_bound` supplies one), so the statement quantifies over every $c>0$ with that property; it is fixed before $\alpha$, as $c=c(s,\Gamma)$ on the page.
-- source:
--   Rachev & Römisch, Quantitative stability in stochastic programming: The method of probability metrics, preprint (edoc.hu-berlin.de), p. 25, proof of Theorem 5.2 ("We conclude that ... for each x ∈ X")

import Mathlib
import Definitions.Def_ProbMetricStab_Portfolio_Setting

open MeasureTheory
open scoped ENNReal

namespace ProbMetricStab.Portfolio
theorem nonsingular_quadratic_growth {s : ℕ} (Γ : Measure (Rs s)) (hΓ : IsSpectral Γ)
    (hns : Nonsingular Γ) :
    ∀ c : ℝ, 0 < c → (∀ x : Rs s, c * ‖x‖ ^ 2 ≤ ∫ ξ in unitSphere s, |(inner ℝ x ξ : ℝ)| ^ 2 ∂Γ) →
      ∀ α : ℝ, 1 < α → α < 2 → ∃ xs : Rs s, solSet α Γ = {xs} ∧ ∀ x ∈ simplex s,
        (1 / 4) * c * α * (α - 1) * ‖x - xs‖ ^ 2 ≤ risk α Γ x - optVal α Γ := by sorry
end ProbMetricStab.Portfolio
