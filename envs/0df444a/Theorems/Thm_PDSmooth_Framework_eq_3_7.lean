-- Prove2me | Theorems.Thm_PDSmooth_Framework_eq_3_7
-- name    : PDSmooth.Framework.eq_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:54:36.038573+00:00
-- url     : https://prove2.me/theorems/23ae301d-3558-4bc3-8863-263cc0c748ed
-- title:
--   Eq. (3.7), p. 11 — the ρ-dually-smoothed f is uniformly within ρR_Y(ω_Y) of f on X
-- statement:
--   Under the standing assumptions of problem (1.1), let $\rho\ge0$ and let $f_\rho(x)=\max_{y\in\mathcal Y}\Phi(x,y)-g(y)-\rho\,\omega_{\mathcal Y}(y)$ be the $\rho$-dually-smoothed version of $f(x)=\max_{y\in\mathcal Y}\Phi(x,y)-g(y)$. Then for every $x\in\mathcal X$,
--
--   $$
--   |f_\rho(x)-f(x)|\le \rho\,R_{\mathcal Y}(\omega_{\mathcal Y}),\qquad R_{\mathcal Y}(\omega_{\mathcal Y})=\sup_{y\in\mathcal Y}|\omega_{\mathcal Y}(y)|.
--   $$
--
--   Dual smoothing thus perturbs $f$ by at most $\rho R_{\mathcal Y}(\omega_{\mathcal Y})$ uniformly on $\mathcal X$; this is what lets Algorithm 1 work with the smoothed objective $q_\rho$ while measuring progress on $q$.
--
--   **Formalization Note** The paper takes $\rho>0$; the statement is given for $\rho\ge0$, which adds only the trivial case $f_0=f$ and covers the value $\rho=0$ that Lean's division assigns to $2\eta/R_{\mathcal Y}(\omega_{\mathcal Y})$ when $R_{\mathcal Y}(\omega_{\mathcal Y})=0$.
-- source:
--   Zhao, A primal-dual smoothing framework for max-structured non-convex optimization, arXiv:2003.04375v5, p. 11, (3.7)

import Mathlib
import Definitions.Def_PDSmooth_Framework_Setting

namespace PDSmooth.Framework

/-- Eq. (3.7), p. 11: for `ρ ≥ 0` and `x ∈ X`, `|f_ρ(x) − f(x)| ≤ ρ R_Y(ω_Y)`. -/
theorem eq_3_7 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ} {ωX : E → ℝ} {ωY : F → ℝ}
    {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (x : E) (hx : x ∈ X) :
    |fSmooth Φ g ωY Y ρ x - fMax Φ g Y x| ≤ ρ * rangeY ωY Y := by sorry
end PDSmooth.Framework
