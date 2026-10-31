-- Prove2me | Theorems.Thm_SalesforceComp_proposition_1
-- name    : SalesforceComp.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:25:22.138409+00:00
-- url     : https://prove2.me/theorems/91a032db-15d8-41fa-8674-724a5e3fc46d
-- title:
--   Proposition 1, p. 9 — (PCD) and (PCS) are bounded by $V^*=\mathbb E_\Theta[M(r^*,Q^*,\Theta)]$, and $(r^*,Q^*)$ maximizes $M(\cdot,\cdot,\theta)$
-- statement:
--   Work in the model of §2 with Assumption 1 (the `Model` definition of this mission): output cost $K(r,\theta)=C(E(r,\theta))$, expected demand $D$, expected sales $S$, inverse hazard rate $H$ on the type support $[\underline\theta,\bar\theta]$, and the virtual surplus $M(r,Q,\theta)=pS(r,Q)-(c+h)Q-K(r,\theta)+K_2(r,\theta)H(\theta)$.
--
--   Let $r^*,Q^*$ be functions with $r^*(\theta)\ge0$, $Q^*(\theta)\ge0$ that solve system (1),
--   $$pS_1(r,Q)-K_1(r,\theta)+K_{12}(r,\theta)H(\theta)=0,\qquad pS_2(r,Q)-c-h=0,$$
--   at every $\theta\in[\underline\theta,\bar\theta]$, and let $V^*=\mathbb E_\Theta[M(r^*(\Theta),Q^*(\Theta),\Theta)]$. Then:
--
--   1. for every $\theta\in[\underline\theta,\bar\theta]$ and all $x\ge0$, $q\ge0$, $M(x,q,\theta)\le M(r^*(\theta),Q^*(\theta),\theta)$;
--   2. every profit attained by a feasible direct mechanism in (PCD), and every profit attained by a feasible direct mechanism in (PCS), is at most $V^*$.
--
--   So the two control problems have the common upper bound $V^*$, the expected virtual surplus of the outcome determined by (1).
--
--   **Formalization Note** The problems range over all feasible direct mechanisms (obedient (IC), (IR), integrability). No uniqueness of the solution of (1) is assumed.
--
--   Differences from the source:
--   - generalization: (PCD) and (PCS) have a common upper bound, where the outcome (r*(θ), Q*(θ)) solves (1) → the bound is named, V* = E_Θ[M(r*(Θ), Q*(Θ), Θ)], and clause 1 adds the pointwise maximization of M established in the proof (p. 22); reason: the stronger statement implies the printed one
--   - reading: the outcome (r*(θ), Q*(θ)) solves system (1) (Proposition 1, p. 9) → r*, Q* are any functions with r*(θ) ≥ 0, Q*(θ) ≥ 0 solving (1) at every θ ∈ [θ̲, θ̄]; uniqueness is not assumed; reason: the paper presupposes a solution; (1) need not determine Q* uniquely (see proposition_1_monotone)
--   - reading: "Let r(θ, θ̂) be the maximizer" (p. 9, p. 12); (IC) π(θ) ≥ π(θ, θ̂) → a direct mechanism names the output (and, under delegation, the inventory request) it expects; (IC) says truthful reporting with these actions pays at least as much as any report θ̂ ∈ [θ̲, θ̄] with any output x ≥ 0 (and any inventory q ≥ 0); each expected action is nonnegative on [θ̲, θ̄]; reason: the maximizer need not be unique for a general T; the obedience form is the standard reading and covers the paper's convention that a non-attained maximum is excluded
--   - encoding: expectations E_ε[T(·)] and E_Θ[·] in the agent's payoff and the firm's profit → feasibility requires ε ↦ T(·) to be G-integrable at every report and action, and the firm's profit integrand to be integrable on [θ̲, θ̄]; E_Θ[φ] = ∫_{θ̲}^{θ̄} φ f; reason: the paper presupposes these expectations exist; without the clauses Lean's integral of a non-integrable function would be 0
--   - generalization: Assumption 1 (C), (D), (E), p. 7, printed without a domain → C, d, E are C³ on ℝ, ℝ², ℝ²; the sign conditions are required only on the domain of the model: E at outputs r ≥ 0 and types θ ∈ [θ̲, θ̄], C at the efforts E(r, θ) these reach, d at outputs r ≥ 0 and G-almost every ε; reason: the action set is r ≥ 0 (p. 9) and the type support is [θ̲, θ̄]; no statement looks outside them, so any reading of the assumption on a domain containing this one specializes to it
--   - encoding: output R(e, θ), with E defined by R(E(r, θ), θ) = r (p. 7) → E is a primitive of the model; R does not appear; reason: the paper says the reformulated model in (r, K) "will be our focus throughout the paper", and Assumption 1 puts no condition on R
--   - reading: H(θ) = (1 − F(θ))/f(θ) decreases in θ (p. 7) → H is antitone (weakly decreasing) on [θ̲, θ̄]; reason: the proof of Proposition 1 uses only H′ ≤ 0
--   - generalization: ε has a distribution G with density g, and all functions are C³ (p. 7) → G is any probability measure on ℝ absolutely continuous w.r.t. Lebesgue measure; no smoothness of g; reason: every C³ density is such a G, so the statement specializes to the source's
--   - encoding: Θ has density f on [θ̲, θ̄]; H divides by f → f measurable, integrable on [θ̲, θ̄] with total mass 1, and f > 0 on [θ̲, θ̄]; reason: the positivity excludes only the undefined values of H
--   - encoding: D(r) = E_ε[d(r, ε)] (p. 8) → ε ↦ d(r, ε) is G-integrable for every r ≥ 0; reason: the expectation is presupposed by its definition
--   - reading: unit price p (p. 6) → p > 0; reason: a unit price; implicit in the paper
--   - encoding: partial derivatives as numbered subscripts (p. 7) → deriv of one-variable slices (pd1, pd2); reason: all functions concerned are differentiable, so the values agree
-- source:
--   Song–Lai–Xiao, Optimal Salesforce Compensation, MSOM (2024), doi:10.1287/msom.2022.0400, Proposition 1, p. 9; proof, Appendix A, pp. 22–23

import Mathlib
import Definitions.Def_SalesforceComp_Model

open MeasureTheory

namespace SalesforceComp

open Model

/-- **Proposition 1** (the common upper bound), Song–Lai–Xiao, MSOM (2024),
doi:10.1287/msom.2022.0400, Proposition 1, p. 9, with its proof, pp. 22–23.

Let `(r*, Q*)` be nonnegative and solve system (1) at every `θ ∈ [θ̲, θ̄]`. Then
1. for every `θ ∈ [θ̲, θ̄]`, `(r*(θ), Q*(θ))` maximizes the virtual surplus `M(·, ·, θ)` over
   `r ≥ 0`, `Q ≥ 0`;
2. every profit attainable in (PCD) and every profit attainable in (PCS) is at most
   `V* = E_Θ[M(r*(Θ), Q*(Θ), Θ)]`.

**Formalization Note.** "(PCD) and (PCS) have a common upper bound, where the outcome
`(r*(θ), Q*(θ))` solves (1)" is stated as clause 2 with the bound named; profits range over all
feasible direct mechanisms. No uniqueness of the solution of (1) is assumed. -/
theorem proposition_1 (M : Model) (rs Qs : ℝ → ℝ) (hsol : M.SolvesFOC rs Qs) :
    (∀ θ ∈ M.I, ∀ x q : ℝ, 0 ≤ x → 0 ≤ q →
      M.virtSurplus x q θ ≤ M.virtSurplus (rs θ) (Qs θ) θ) ∧
    (∀ v ∈ M.profitsCD, v ≤ M.Vstar rs Qs) ∧ (∀ v ∈ M.profitsCS, v ≤ M.Vstar rs Qs) := by sorry

end SalesforceComp
