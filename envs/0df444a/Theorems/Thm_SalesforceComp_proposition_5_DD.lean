-- Prove2me | Theorems.Thm_SalesforceComp_proposition_5_DD
-- name    : SalesforceComp.proposition_5_DD
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:25:38.876228+00:00
-- url     : https://prove2.me/theorems/e136bf06-3dae-4a3c-b6b9-2d56bf7f6f46
-- title:
--   Proposition 5, p. 13 — under Condition (D) the menu $T_{DD}$ is optimal for (PDD) and earns $V^*$
-- statement:
--   Work in the model of §2 with Assumption 1 (the `Model` definition of this mission): output cost $K(r,\theta)=C(E(r,\theta))$, expected demand $D$, expected sales $S$, inverse hazard rate $H$ on the type support $[\underline\theta,\bar\theta]$, and the virtual surplus $M(r,Q,\theta)=pS(r,Q)-(c+h)Q-K(r,\theta)+K_2(r,\theta)H(\theta)$.
--
--   Let $r^*,Q^*$ be functions with $r^*(\theta)\ge0$, $Q^*(\theta)\ge0$ that solve system (1),
--   $$pS_1(r,Q)-K_1(r,\theta)+K_{12}(r,\theta)H(\theta)=0,\qquad pS_2(r,Q)-c-h=0,$$
--   at every $\theta\in[\underline\theta,\bar\theta]$, and let $V^*=\mathbb E_\Theta[M(r^*(\Theta),Q^*(\Theta),\Theta)]$. Suppose Condition (D) holds. With $\alpha_{DD}=\alpha_{CD}$ as in Proposition 3,
--   $$\gamma_{DD}(\theta)=2Q^*(\theta)+h,\qquad \beta_{DD}(\theta)=-\alpha_{DD}(\theta)D(r^*(\theta))+K(r^*(\theta),\theta)+hQ^*(\theta)-\int_{\underline\theta}^{\theta}K_2(r^*(z),z)\,dz-\gamma_{DD}(\theta)Q^*(\theta)+Q^*(\theta)^2,$$
--   consider the delegation mechanism with payment $T_{DD}(d,Q,\theta)=\alpha_{DD}(\theta)d+\beta_{DD}(\theta)+\gamma_{DD}(\theta)Q-Q^2$, expected output $r^*$ and expected inventory request $Q^*$. Then:
--
--   1. it is feasible for (PDD);
--   2. its profit equals $V^*$;
--   3. its profit is the largest profit of any feasible direct mechanism of (PDD).
--
--   A quadratic inventory term in the base payment aligns the agent's inventory request, so delegation costs the firm nothing when demand is contractible.
--
--   Differences from the source:
--   - reading: the optimal MLC for (PDD) is characterized by the stated coefficients and implements the second-best outcome → the menu is feasible for (PDD), its profit equals V* = E_Θ[M(r*(Θ), Q*(Θ), Θ)], and that profit is the greatest element of the set of profits of all feasible direct mechanisms of (PDD); reason: "optimal" and "implements the second-best outcome" mean attaining the upper bound of Proposition 1 over all mechanisms
--   - generalization: Condition (D): d/dθ[K₁(r*(θ), θ)/D₁(r*(θ))] ≥ 0 on [θ̲, θ̄] (p. 10) → θ ↦ K₁(r*(θ), θ)/D₁(r*(θ)) is monotone (nondecreasing) on [θ̲, θ̄]; reason: a nonnegative derivative implies monotonicity; the monotone form needs no differentiability of r*
--   - reading: the outcome (r*(θ), Q*(θ)) solves system (1) (Proposition 1, p. 9) → r*, Q* are any functions with r*(θ) ≥ 0, Q*(θ) ≥ 0 solving (1) at every θ ∈ [θ̲, θ̄]; uniqueness is not assumed; reason: the paper presupposes a solution; (1) need not determine Q* uniquely (see proposition_1_monotone)
--   - reading: "Let r(θ, θ̂) be the maximizer" (p. 9, p. 12); (IC) π(θ) ≥ π(θ, θ̂) → a direct mechanism names the output (and, under delegation, the inventory request) it expects; (IC) says truthful reporting with these actions pays at least as much as any report θ̂ ∈ [θ̲, θ̄] with any output x ≥ 0 (and any inventory q ≥ 0); each expected action is nonnegative on [θ̲, θ̄]; reason: the maximizer need not be unique for a general T; the obedience form is the standard reading and covers the paper's convention that a non-attained maximum is excluded
--   - encoding: expectations E_ε[T(·)] and E_Θ[·] in the agent's payoff and the firm's profit → feasibility requires ε ↦ T(·) to be G-integrable at every report and action, and the firm's profit integrand to be integrable on [θ̲, θ̄]; E_Θ[φ] = ∫_{θ̲}^{θ̄} φ f; reason: the paper presupposes these expectations exist; without the clauses Lean's integral of a non-integrable function would be 0
--   - reading: Π(T) = E_{Θ,ε}[pS(r(Θ), Q(Θ)) − cQ(Θ) − T(d(r(Θ), ε), Θ)] (p. 12), with T printed without its inventory argument → the payment in the firm's profit is T(d(r(Θ), ε), Q(Θ), Θ) (DD) and T(min{d(r(Θ), ε), Q(Θ)}, Q(Θ), Θ) (DS); reason: T has three arguments in §4 (p. 11); the printed formula omits one by a slip
--   - generalization: Assumption 1 (C), (D), (E), p. 7, printed without a domain → C, d, E are C³ on ℝ, ℝ², ℝ²; the sign conditions are required only on the domain of the model: E at outputs r ≥ 0 and types θ ∈ [θ̲, θ̄], C at the efforts E(r, θ) these reach, d at outputs r ≥ 0 and G-almost every ε; reason: the action set is r ≥ 0 (p. 9) and the type support is [θ̲, θ̄]; no statement looks outside them, so any reading of the assumption on a domain containing this one specializes to it
--   - encoding: output R(e, θ), with E defined by R(E(r, θ), θ) = r (p. 7) → E is a primitive of the model; R does not appear; reason: the paper says the reformulated model in (r, K) "will be our focus throughout the paper", and Assumption 1 puts no condition on R
--   - reading: H(θ) = (1 − F(θ))/f(θ) decreases in θ (p. 7) → H is antitone (weakly decreasing) on [θ̲, θ̄]; reason: the proof of Proposition 1 uses only H′ ≤ 0
--   - generalization: ε has a distribution G with density g, and all functions are C³ (p. 7) → G is any probability measure on ℝ absolutely continuous w.r.t. Lebesgue measure; no smoothness of g; reason: every C³ density is such a G, so the statement specializes to the source's
--   - encoding: Θ has density f on [θ̲, θ̄]; H divides by f → f measurable, integrable on [θ̲, θ̄] with total mass 1, and f > 0 on [θ̲, θ̄]; reason: the positivity excludes only the undefined values of H
--   - encoding: D(r) = E_ε[d(r, ε)] (p. 8) → ε ↦ d(r, ε) is G-integrable for every r ≥ 0; reason: the expectation is presupposed by its definition
--   - reading: unit price p (p. 6) → p > 0; reason: a unit price; implicit in the paper
--   - encoding: partial derivatives as numbered subscripts (p. 7) → deriv of one-variable slices (pd1, pd2); reason: all functions concerned are differentiable, so the values agree
-- source:
--   Song–Lai–Xiao, Optimal Salesforce Compensation, MSOM (2024), doi:10.1287/msom.2022.0400, Proposition 5, p. 13; proof, Appendix A, pp. 24–25

import Mathlib
import Definitions.Def_SalesforceComp_Model

open MeasureTheory

namespace SalesforceComp

open Model

/-- **Proposition 5, demand-based delegation (DD)**, Song–Lai–Xiao, MSOM (2024),
doi:10.1287/msom.2022.0400, Proposition 5, p. 13; proof, pp. 24–25.

Let `(r*, Q*)` be nonnegative and solve (1) on `[θ̲, θ̄]`, and let Condition (D) hold. Then the
menu `T_DD(d, Q, θ) = α_DD(θ)d + β_DD(θ) + γ_DD(θ)Q − Q²` of Proposition 5, with expected output
`r*` and expected inventory request `Q*`, is feasible for (PDD), earns the firm
`V* = E_Θ[M(r*, Q*, Θ)]`, and that profit is the largest attainable in (PDD). -/
theorem proposition_5_DD (M : Model) (rs Qs : ℝ → ℝ) (hsol : M.SolvesFOC rs Qs)
    (hD : M.CondD rs) :
    M.FeasibleDD (M.mechDD rs Qs) ∧ M.profitDD (M.mechDD rs Qs) = M.Vstar rs Qs ∧
      IsGreatest M.profitsDD (M.profitDD (M.mechDD rs Qs)) := by sorry

end SalesforceComp
