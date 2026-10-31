-- Prove2me | Theorems.Thm_RiskExpPG_corollary_1
-- name    : RiskExpPG.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:25:32.910631+00:00
-- url     : https://prove2.me/theorems/9753c561-e075-4362-91c9-a10de38fdc98
-- title:
--   Corollary 1 — $\Lambda$ is the unique fixed point of the cycle equation, and $h$ is a cycle expectation
-- statement:
--   Let $P$ be an irreducible aperiodic transition matrix on a finite set, $C$ a one-step cost, $\alpha>0$, and $x^*$ a state. With $\tau_{x^*}:=\inf\{i\ge1:\Phi_i=x^*\}$, the risk-sensitive cost $\Lambda(\alpha)$ is the unique fixed point of
--   $$E^P_{\Phi_0=x^*}\Big[\exp\Big(\sum_{i=0}^{\tau_{x^*}-1}(\alpha C(\Phi_i)-\Lambda)\Big)\Big]=1.$$
--   Moreover, for any $x$, the relative value function, that is the positive solution of the multiplicative Poisson equation
--   $$h(x)=\frac{\exp(\alpha C(x))}{\exp(\Lambda(\alpha))}\sum_{y}P(x,y)h(y)$$
--   with $h(x^*)=1$, exists and is given by
--   $$h(x)=E^P_{\Phi_0=x}\Big[\exp\Big(\sum_{i=0}^{\tau_{x^*}-1}(\alpha C(\Phi_i)-\Lambda(\alpha))\Big)\Big].$$
--
--   This is the description of the cost through cycles on which the algorithm is built.
--
--   Differences from the source:
--   - reading: x* a recurrent state, h the eigenvector of (15) → x* any state of a primitive chain, h a positive solution of (15) with h(x*) = 1; reason: every state of such a chain is recurrent; Eq. (3) fixes this normalization of h
--   - encoding: expectations over the first return time τ_{x*} → sums over finite excursions, in ℝ≥0∞ or as a real sum with its summability asserted; reason: Assumption 1 makes τ_{x*} finite almost surely, so the values agree and +∞ stays representable
-- source:
--   Moharrami, Murthy, Roy & Srikant, A Policy Gradient Algorithm for the Risk-Sensitive Exponential Cost MDP, arXiv:2202.04157v2, Corollary 1, p.17; Eq. (15), p.16; Eq. (3), p.4

import Mathlib
import Definitions.Def_RiskExpPG_Chain

open Filter Topology MeasureTheory
open scoped ENNReal

namespace RiskExpPG

/-- **Corollary 1** (arXiv:2202.04157v2, p.17). For a primitive stochastic matrix `Q`, the
risk-sensitive cost `Λ(α)` is the unique fixed point of
`E^Q_{Φ₀ = x*}[exp(Σ_{i<τ_{x*}} (α c(Φᵢ) - Λ))] = 1`. Moreover, the positive solution `h` of the
multiplicative Poisson equation (15) (p.16) with the normalization `h(x*) = 1` of Eq. (3) exists, and
any such `h` is given by `h(x) = E^Q_{Φ₀ = x}[exp(Σ_{i<τ_{x*}} (α c(Φᵢ) - Λ(α)))]`. -/
theorem corollary_1 {X : Type*} [Fintype X] [DecidableEq X] (Q : Matrix X X ℝ)
    (hQ : IsStochastic Q) (hprim : Matrix.IsPrimitive Q) (c : X → ℝ) (α : ℝ) (hα : 0 < α)
    (xstar : X) :
    (∀ Λ : ℝ, cycleMgf Q c α xstar Λ xstar = 1 ↔ Λ = riskRate Q c α xstar) ∧
    (∃ h : X → ℝ, (∀ x, 0 < h x) ∧ h xstar = 1 ∧
      ∀ x, h x = Real.exp (α * c x) / Real.exp (riskRate Q c α xstar) * ∑ y, Q x y * h y) ∧
    ∀ h : X → ℝ, (∀ x, 0 < h x) → h xstar = 1 →
      (∀ x, h x = Real.exp (α * c x) / Real.exp (riskRate Q c α xstar) * ∑ y, Q x y * h y) →
      ∀ x, cycleMgf Q c α xstar (riskRate Q c α xstar) x = ENNReal.ofReal (h x) := by sorry

end RiskExpPG
