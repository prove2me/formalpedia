-- Prove2me | Theorems.Thm_RUCVaR_MinFormula_Supplement_theorem_16
-- name    : RUCVaR.MinFormula.Supplement.theorem_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:15:41.009802+00:00
-- url     : https://prove2.me/theorems/b322b0ff-2ada-489c-b53a-12731511695c
-- title:
--   Theorem 16, p. 21 — risk shaping: CVaR constraints φ_{β_i}(x) ≤ ω_i become F_{β_i}(x, α_i) ≤ ω_i (corrected: activity needs α*_i ∈ argmin)
-- statement:
--   Let $P$ be a Borel probability measure on $\mathbb R^m$, the law of a random vector $y$, let $X\subseteq\mathbb R^n$ be a set of decisions, and let $f(x,y)$ be the loss of decision $x$ under outcome $y$. Assume that $f(x,y)$ is continuous in $x$ on $X$ for every $y$, measurable in $y$ for every $x$, and that $E\{|f(x,y)|\}<\infty$ for every $x\in X$. For a confidence level $\beta\in(0,1)$ write $\phi_\beta(x)$ for the $\beta$-CVaR of the loss $f(x,y)$ (the mean of its $\beta$-tail distribution, Definition 3) and $F_\beta(x,\alpha)=\alpha+(1-\beta)^{-1}E\{[f(x,y)-\alpha]^+\}$.
--
--   Let $l\ge0$, let $\beta_1,\dots,\beta_l\in(0,1)$ be probability thresholds, $\omega_1,\dots,\omega_l\in\mathbb R$ loss tolerances, and $g:\mathbb R^n\to\mathbb R$ any objective function. Consider the problems
--   $$
--   \text{(46)}\qquad \text{minimize } g(x) \text{ over } x\in X \text{ satisfying } \phi_{\beta_i}(x)\le\omega_i,\ i=1,\dots,l,
--   $$
--   $$
--   \text{(47)}\qquad \text{minimize } g(x) \text{ over } (x,\alpha_1,\dots,\alpha_l)\in X\times\mathbb R^l \text{ satisfying } F_{\beta_i}(x,\alpha_i)\le\omega_i,\ i=1,\dots,l .
--   $$
--   A point solves a problem when it is feasible and its objective value is at most that of every feasible point.
--
--   **Theorem 16 (risk shaping with CVaR).** For every $x^*\in\mathbb R^n$ and $\alpha^*\in\mathbb R^l$:
--
--   1. $(x^*,\alpha^*_1,\dots,\alpha^*_l)$ solves (47) if and only if $x^*$ solves (46) and $F_{\beta_i}(x^*,\alpha^*_i)\le\omega_i$ for $i=1,\dots,l$;
--   2. if $(x^*,\alpha^*)$ solves (47), then $\phi_{\beta_i}(x^*)\le\omega_i$ for every $i$, and
--   $$
--   \phi_{\beta_i}(x^*)=\omega_i\quad\text{for each } i \text{ such that } F_{\beta_i}(x^*,\alpha^*_i)=\omega_i \text{ and } \alpha^*_i\in\operatorname*{argmin}_{\alpha\in\mathbb R}F_{\beta_i}(x^*,\alpha).
--   $$
--
--   The theorem says that any number of CVaR constraints, at different confidence levels, can be imposed on a decision problem by adding one real variable per constraint and replacing each CVaR by the expectation-type function $F_{\beta_i}$; when $X$, $g$ and $f(\cdot,y)$ are convex the result is a convex program.
--
--   **Formalization Note** The objective $g$ is an arbitrary real function (only its values on $X$ matter); the number of constraints $l$ may be $0$. The thresholds $\beta_i$ lie in $(0,1)$ individually, as the standing setting requires of a confidence level.
--
--   Differences from the source:
--   - correction: "actually $\phi_{\beta_i}(x^*)=\omega_i$ for each $i$ such that $F_{\beta_i}(x^*,\alpha^*_i)=\omega_i$" → the same equality for each $i$ such that $F_{\beta_i}(x^*,\alpha^*_i)=\omega_i$ and $\alpha^*_i$ minimizes $F_{\beta_i}(x^*,\cdot)$; reason: the printed clause is false. Take $X=\{x_0\}$, $g\equiv0$, $l=1$, a loss with $\phi_{\beta_1}(x_0)=0$ (for instance $f\equiv0$) and $\omega_1=1$. By Theorem 10, $F_{\beta_1}(x_0,\cdot)$ is continuous with minimum value $0$, and $F_{\beta_1}(x_0,\alpha)\ge\alpha$ tends to $+\infty$, so some $\alpha^*_1$ has $F_{\beta_1}(x_0,\alpha^*_1)=1=\omega_1$. Then $(x_0,\alpha^*_1)$ solves (47), yet $\phi_{\beta_1}(x_0)=0\ne\omega_1$. The proof on p. 21 rests on (48), $\phi_{\beta_i}(x)=\min_{\alpha_i}F_{\beta_i}(x,\alpha_i)$, which gives the equality exactly when $\alpha^*_i$ attains that minimum; the added premise excludes only the solutions of (47) whose $\alpha^*_i$ is not a minimizer.
--   - encoding: $P$ a Borel probability measure on a set $Y\subseteq\mathbb R^m$ → $P$ a Borel probability measure on $\mathbb R^m$; reason: a law on $Y$ is a law on $\mathbb R^m$ concentrated on $Y$, and the statement does not use $Y$.
--   - encoding: $g$ "any objective function chosen on $X$" → $g:\mathbb R^n\to\mathbb R$; reason: only the values of $g$ on $X$ enter (46) and (47), and every function on $X$ extends to $\mathbb R^n$.
-- source:
--   Rockafellar & Uryasev, Conditional value-at-risk for general loss distributions, Research Report #2001-5, Univ. of Florida, April 4, 2001, p. 21, Theorem 16, (46)–(48); standing setting p. 5

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_RUCVaR_MinFormula_Setting
open MeasureTheory

namespace RUCVaR.MinFormula.Supplement

/-- Theorem 16 (risk-shaping with CVaR), p. 21, (46)–(47), with the last clause corrected: the
equality `φ_{β_i}(x*) = ω_i` is asserted for each `i` with `F_{β_i}(x*, α*_i) = ω_i` and
`α*_i ∈ argmin_α F_{β_i}(x*, α)`.

A point `x` is feasible for (46) when `x ∈ X` and `φ_{β_i}(x) ≤ ω_i` for all `i`, and solves (46)
when it is feasible and `g x ≤ g x'` for every feasible `x'`. A pair `(x, α)` is feasible for (47)
when `x ∈ X` and `F_{β_i}(x, α_i) ≤ ω_i` for all `i`, and solves (47) when it is feasible and
`g x ≤ g x'` for every feasible `(x', α')`. -/
theorem theorem_16 {m n l : ℕ} (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (X : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (hf_cont : ∀ y, ContinuousOn (fun x => f x y) X) (hf_meas : ∀ x, Measurable (f x))
    (hf_int : ∀ x ∈ X, Integrable (f x) P)
    (β : Fin l → ℝ) (hβ0 : ∀ i, 0 < β i) (hβ1 : ∀ i, β i < 1) (ω : Fin l → ℝ)
    (g : (Fin n → ℝ) → ℝ) (xs : Fin n → ℝ) (αs : Fin l → ℝ) :
    -- (x*, α*) solves (47)
    (((xs ∈ X ∧ ∀ i, RUCVaR.MinFormula.Fbeta P f (β i) xs (αs i) ≤ ω i) ∧
        ∀ (x' : Fin n → ℝ) (α' : Fin l → ℝ),
          (x' ∈ X ∧ ∀ i, RUCVaR.MinFormula.Fbeta P f (β i) x' (α' i) ≤ ω i) → g xs ≤ g x') ↔
      -- x* solves (46)
      (((xs ∈ X ∧ ∀ i, RUCVaR.MinFormula.CVaR P f (β i) xs ≤ ω i) ∧
          ∀ x' : Fin n → ℝ,
            (x' ∈ X ∧ ∀ i, RUCVaR.MinFormula.CVaR P f (β i) x' ≤ ω i) → g xs ≤ g x') ∧
        -- and F_{β_i}(x*, α*_i) ≤ ω_i for every i
        ∀ i, RUCVaR.MinFormula.Fbeta P f (β i) xs (αs i) ≤ ω i)) ∧
    -- Moreover, for a solution (x*, α*) of (47):
    (((xs ∈ X ∧ ∀ i, RUCVaR.MinFormula.Fbeta P f (β i) xs (αs i) ≤ ω i) ∧
        ∀ (x' : Fin n → ℝ) (α' : Fin l → ℝ),
          (x' ∈ X ∧ ∀ i, RUCVaR.MinFormula.Fbeta P f (β i) x' (α' i) ≤ ω i) → g xs ≤ g x') →
      (∀ i, RUCVaR.MinFormula.CVaR P f (β i) xs ≤ ω i) ∧
      ∀ i, RUCVaR.MinFormula.Fbeta P f (β i) xs (αs i) = ω i →
        IsMinOn (RUCVaR.MinFormula.Fbeta P f (β i) xs) Set.univ (αs i) →
        RUCVaR.MinFormula.CVaR P f (β i) xs = ω i) := by sorry

end RUCVaR.MinFormula.Supplement
