-- Prove2me | Theorems.Thm_RiskExpPG_proposition_2
-- name    : RiskExpPG.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:25:29.589903+00:00
-- url     : https://prove2.me/theorems/9292f1a6-aba8-4f30-b671-87143bf2fafe
-- title:
--   Proposition 2 — $\exp(\Lambda)$ is the largest eigenvalue of $\widehat P$
-- statement:
--   Let $P$ be an irreducible aperiodic transition matrix on a finite set, $C$ a one-step cost and $\alpha>0$. Then the limit
--   $$\Lambda(\alpha)=\lim_{n\to\infty}\frac1n\ln E^P_{\Phi_0=x}\Big[\exp\Big(\alpha\sum_{i=0}^{n-1}C(\Phi_i)\Big)\Big]$$
--   exists and has the same value for every initial state $x$, and $\exp(\Lambda(\alpha))$ is the largest eigenvalue of $\widehat P:=\mathrm{diag}(e^{\alpha C})P$.
--
--   This identifies the risk-sensitive cost as a spectral quantity, and it is the reason the limit does not depend on the initial state.
--
--   Differences from the source:
--   - reading: a chain that is recurrent and aperiodic (App. A.1, p.14) → Matrix.IsPrimitive; reason: App. A calls these the matrices with a unique stationary distribution, so recurrent means irreducible here; for such a stochastic matrix this is primitivity
--   - reading: the largest eigenvalue → an eigenvalue such that every other complex eigenvalue has strictly smaller modulus; reason: the proof on p.15 uses exactly |λ̂_l| < λ̂₁ for all other eigenvalues
--   - encoding: a state space with a state x → Nonempty X; reason: an empty state space has no eigenvalue; no instance of the page is excluded
-- source:
--   Moharrami, Murthy, Roy & Srikant, A Policy Gradient Algorithm for the Risk-Sensitive Exponential Cost MDP, arXiv:2202.04157v2, Proposition 2, p.15

import Mathlib
import Definitions.Def_RiskExpPG_Chain

open Filter Topology MeasureTheory
open scoped ENNReal

namespace RiskExpPG

/-- **Proposition 2** (arXiv:2202.04157v2, p.15). For a primitive stochastic matrix `Q`, a cost `c`
and `α > 0`, the limit in Eq. (13) exists and has the same value `Λ` from every initial state, and
`exp Λ` is the largest eigenvalue of `P̂ := diag(e^{αc}) Q`: it is an eigenvalue, and every other
complex eigenvalue has strictly smaller modulus. -/
theorem proposition_2 {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] (Q : Matrix X X ℝ)
    (hQ : IsStochastic Q) (hprim : Matrix.IsPrimitive Q) (c : X → ℝ) (α : ℝ) (hα : 0 < α) :
    ∃ Λ : ℝ,
      (∀ x, Tendsto (fun n : ℕ => (1 / (n : ℝ)) * Real.log (expMoment Q c α x n)) atTop (𝓝 Λ)) ∧
      ((Real.exp Λ : ℝ) : ℂ) ∈ spectrum ℂ ((tilted Q c α).map (algebraMap ℝ ℂ)) ∧
      ∀ μ ∈ spectrum ℂ ((tilted Q c α).map (algebraMap ℝ ℂ)),
        μ ≠ ((Real.exp Λ : ℝ) : ℂ) → ‖μ‖ < Real.exp Λ := by sorry

end RiskExpPG
