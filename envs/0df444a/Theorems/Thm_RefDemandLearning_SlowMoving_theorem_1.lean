-- Prove2me | Theorems.Thm_RefDemandLearning_SlowMoving_theorem_1
-- name    : RefDemandLearning.SlowMoving.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T05:25:17.013014+00:00
-- url     : https://prove2.me/theorems/e8888325-d1e9-468a-937b-20bfda6e3e35
-- title:
--   Theorem 1 — loss under the fixed price $α/(2β)$
-- statement:
--   Fix the Section 2 price interval and known demand-parameter bounds. Assume the loss-averse parameter set $\Theta$ is nonempty, has positive slope and nonnegative sensitivities, ensures nonnegative expected demand on the box, and places $\alpha/(2\beta)$ in its interior for every parameter vector. Let $\theta=(\alpha,\beta,\eta^+,\eta^-)\in\Theta$ and let $\rho\in\mathcal R_{ES}$: for some $\zeta\in[0,1)$, its continuous interval-valued reference maps obey exponential smoothing after every history.
--
--   There exists a finite positive constant $c_1$ such that
--   $$\Pi^*(T,\rho,\theta)-\sum_{t=1}^{T}R\!\left(\frac\alpha{2\beta},\rho_t\!\left(\frac\alpha{2\beta},\ldots,\frac\alpha{2\beta}\right),\theta\right)\le c_1\quad\text{for all integers }T\ge1.$$
--   Here $R(p,r,\theta)=p[\alpha-\beta p+\eta^+(r-p)^+-\eta^-(p-r)^+]$ and $\Pi^*$ is the supremum over every feasible dynamic price vector. Thus the fixed reference-free optimal price loses only a horizon-independent amount against the full dynamic benchmark. The constant can depend on the mechanism and parameter vector. The case $\zeta=0$ is included.
--
--   **Formalization Note.** This deterministic comparison needs no noise law or learning-policy assumptions. Its supremum is finite by compactness and continuity.
--
--   Differences from the source:
--   - encoding: periods start at 1 and positive integer horizons → period n represents source period n+1; horizons and interval endpoints retain explicit positive-natural guards; reason: finite histories use Fin n and finite sums are reindexed without changing any term
--   - encoding: supremum over real price vectors and feasible fixed-price histories → Fin T interval-valued vectors and the same constant path via identity interval clipping; reason: the entire continuous price box is retained, and the fixed price is interior by the standing assumptions
-- source:
--   den Boer and Keskin, Dynamic Pricing with Demand Learning and Reference Effects, DOI https://doi.org/10.1287/mnsc.2021.4234, supplied April 19, 2021 artifact, Theorem 1, printed p. 10, PDF p. 10

import Definitions.Def_RefDemandLearning_SlowMoving_Regret

set_option autoImplicit false

namespace RefDemandLearning.SlowMoving

theorem theorem_1 (B : Bounds) (hB : Standing B) (ρ : Mechanism B.prices)
    (hρ : IsES ρ) (θ : Parameters) (hθ : InTheta B θ) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ T : ℕ, 1 ≤ T →
      fixedRegret B ρ θ (optimalBasePrice θ) T ≤ c₁ := by sorry

end RefDemandLearning.SlowMoving
