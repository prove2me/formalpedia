-- Prove2me | Theorems.Thm_SalesforceComp_lemma_2
-- name    : SalesforceComp.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:25:27.651822+00:00
-- url     : https://prove2.me/theorems/f5ac0bfd-9288-4633-a45b-0f613d741651
-- title:
--   Lemma 2, p. 21 — the envelope identity in integral form and $\Pi=\mathbb E_\Theta[M]-\pi(\underline\theta)$, in all four problems (corrected: integral form)
-- statement:
--   Work in the model of §2 with Assumption 1 (the `Model` definition of this mission): output cost $K(r,\theta)=C(E(r,\theta))$, expected demand $D$, expected sales $S$, inverse hazard rate $H$ on the type support $[\underline\theta,\bar\theta]$, and the virtual surplus $M(r,Q,\theta)=pS(r,Q)-(c+h)Q-K(r,\theta)+K_2(r,\theta)H(\theta)$.
--
--   In each of the problems (PCD), (PCS), (PDD) and (PDS), let a direct mechanism be feasible, with expected output $r(\theta)$, inventory $Q(\theta)$, and truthful obedient payoff $\pi(\theta)$ of the $\theta$-type agent. Then:
--
--   1. for every $\theta\in[\underline\theta,\bar\theta]$,
--   $$\pi(\theta)=\pi(\underline\theta)-\int_{\underline\theta}^{\theta}K_2(r(z),z)\,dz;$$
--   2. $\mathbb E_\Theta[\pi(\Theta)]=\pi(\underline\theta)-\mathbb E_\Theta[K_2(r(\Theta),\Theta)H(\Theta)]$;
--   3. the firm's profit is
--   $$\Pi=\mathbb E_\Theta\big[M(r(\Theta),Q(\Theta),\Theta)\big]-\pi(\underline\theta).$$
--
--   Clause 3 is the identity from which the paper concludes that it is without loss of optimality to induce $\pi(\underline\theta)=0$: (IR) gives $\pi(\underline\theta)\ge0$. It reduces every problem to maximizing the expected virtual surplus.
--
--   **Formalization Note** Expectations over $\Theta$ are $\int_{\underline\theta}^{\bar\theta}\varphi f$. The derivative statement $\pi'(\theta)=-K_2(r(\theta),\theta)$ is replaced by its integral form, which holds for every feasible mechanism.
--
--   Differences from the source:
--   - correction: π′(θ) = −K₂(r(θ), θ) for every θ (p. 21) → π(θ) = π(θ̲) − ∫_{θ̲}^{θ} K₂(r(z), z) dz for every θ ∈ [θ̲, θ̄] (π′ = −K₂ almost everywhere); reason: pointwise differentiability is false for a general feasible mechanism: with d = r + ε (E ε = 0), C = exp, E = r − θ, Θ ~ U[1,2], h = 1, Q ≡ 0, T(d, θ̂) = d for θ̂ < 3/2 and 2d − 1/2 − 2 ln 2 for θ̂ ≥ 3/2, r(θ) = θ + ln a(θ) with a = 1 below 3/2 and 2 from 3/2 on, the mechanism is feasible and π(θ) = max{θ − 1, 2θ − 5/2} has a kink at 3/2
--   - reading: Consequently, it is without loss of optimality for the firm to restrict to compensation schemes that induce π(θ̲) = 0 → Π = E_Θ[M(r(Θ), Q(Θ), Θ)] − π(θ̲); reason: this is the display on p. 22 from which the paper draws the consequence; with (IR), π(θ̲) ≥ 0, it is exactly the content of the sentence
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
--   Song–Lai–Xiao, Optimal Salesforce Compensation, MSOM (2024), doi:10.1287/msom.2022.0400, Appendix A, Lemma 2, p. 21; proof pp. 21–22 (the profit display at the top of p. 22)

import Mathlib
import Definitions.Def_SalesforceComp_Model

open MeasureTheory

namespace SalesforceComp

open Model

/-- **Lemma 2** (the payoff identity, all four problems), Song–Lai–Xiao, MSOM (2024),
doi:10.1287/msom.2022.0400, Appendix A, Lemma 2, p. 21, with its proof, pp. 21–22.

For every feasible mechanism of (PCD), (PCS), (PDD) or (PDS), with `π(θ)` the truthful, obedient
payoff of the `θ`-type agent:
1. `π(θ) = π(θ̲) − ∫_{θ̲}^θ K₂(r(z), z) dz` for every `θ ∈ [θ̲, θ̄]`;
2. `E_Θ[π(Θ)] = π(θ̲) − E_Θ[K₂(r(Θ), Θ)H(Θ)]`;
3. the firm's profit is `Π = E_Θ[M(r(Θ), Q(Θ), Θ)] − π(θ̲)` (the display at the top of p. 22),
   so, with (IR) at `θ̲`, it is without loss of optimality to induce `π(θ̲) = 0`.

**Formalization Note.** The paper's `π′(θ) = −K₂(r(θ), θ)` is stated in integral form
(clause 1): pointwise it is false for a general incentive-compatible mechanism, whose `π` can
have kinks. Expectations over `Θ` are `∫_{θ̲}^{θ̄} φ f`. -/
theorem lemma_2 (M : Model) :
    (∀ m : MechCD, M.FeasibleCD m →
      (∀ θ ∈ M.I, M.rentCD m θ = M.rentCD m M.θlo - ∫ z in M.θlo..θ, pd2 M.K (m.r z) z) ∧
      M.expect (M.rentCD m) =
        M.rentCD m M.θlo - M.expect (fun θ => pd2 M.K (m.r θ) θ * M.H θ) ∧
      M.profitCD m = M.expect (fun θ => M.virtSurplus (m.r θ) (m.Q θ) θ) - M.rentCD m M.θlo) ∧
    (∀ m : MechCS, M.FeasibleCS m →
      (∀ θ ∈ M.I, M.rentCS m θ = M.rentCS m M.θlo - ∫ z in M.θlo..θ, pd2 M.K (m.r z) z) ∧
      M.expect (M.rentCS m) =
        M.rentCS m M.θlo - M.expect (fun θ => pd2 M.K (m.r θ) θ * M.H θ) ∧
      M.profitCS m = M.expect (fun θ => M.virtSurplus (m.r θ) (m.Q θ) θ) - M.rentCS m M.θlo) ∧
    (∀ m : MechDD, M.FeasibleDD m →
      (∀ θ ∈ M.I, M.rentDD m θ = M.rentDD m M.θlo - ∫ z in M.θlo..θ, pd2 M.K (m.r z) z) ∧
      M.expect (M.rentDD m) =
        M.rentDD m M.θlo - M.expect (fun θ => pd2 M.K (m.r θ) θ * M.H θ) ∧
      M.profitDD m = M.expect (fun θ => M.virtSurplus (m.r θ) (m.Q θ) θ) - M.rentDD m M.θlo) ∧
    (∀ m : MechDS, M.FeasibleDS m →
      (∀ θ ∈ M.I, M.rentDS m θ = M.rentDS m M.θlo - ∫ z in M.θlo..θ, pd2 M.K (m.r z) z) ∧
      M.expect (M.rentDS m) =
        M.rentDS m M.θlo - M.expect (fun θ => pd2 M.K (m.r θ) θ * M.H θ) ∧
      M.profitDS m = M.expect (fun θ => M.virtSurplus (m.r θ) (m.Q θ) θ) - M.rentDS m M.θlo) := by sorry

end SalesforceComp
