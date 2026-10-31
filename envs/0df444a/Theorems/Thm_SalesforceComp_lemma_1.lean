-- Prove2me | Theorems.Thm_SalesforceComp_lemma_1
-- name    : SalesforceComp.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:25:19.127147+00:00
-- url     : https://prove2.me/theorems/f4f3015d-2044-4d0e-b73b-fdc4efbcfba6
-- title:
--   Lemma 1, p. 21 — $K_1>0$, $K_2<0$, $K_{11}>0$, $K_{12}<0$, $K_{112}\le0$, $K_{122}\ge0$
-- statement:
--   Work in the model of §2 with Assumption 1 (the `Model` definition of this mission): output cost $K(r,\theta)=C(E(r,\theta))$, expected demand $D$, expected sales $S$, inverse hazard rate $H$ on the type support $[\underline\theta,\bar\theta]$, and the virtual surplus $M(r,Q,\theta)=pS(r,Q)-(c+h)Q-K(r,\theta)+K_2(r,\theta)H(\theta)$.
--
--   The cost function $K(r,\theta)=C(E(r,\theta))$ satisfies, at every output $r\ge0$ and type $\theta\in[\underline\theta,\bar\theta]$,
--   $$K_1>0,\quad K_2<0,\quad K_{11}>0,\quad K_{12}<0,\quad K_{112}\le0,\quad K_{122}\ge0,$$
--   where numbered subscripts are partial derivatives in the respective variables.
--
--   These signs say that output is costly and increasingly so, that a higher type produces more cheaply, and that the type's advantage grows with output; every later step of the analysis uses them.
--
--   **Formalization Note** The partial derivatives are derivatives of one-variable slices; $K$ is $C^3$, so they are genuine.
--
--   Differences from the source:
--   - generalization: Assumption 1 (C), (D), (E), p. 7, printed without a domain → C, d, E are C³ on ℝ, ℝ², ℝ²; the sign conditions are required only on the domain of the model: E at outputs r ≥ 0 and types θ ∈ [θ̲, θ̄], C at the efforts E(r, θ) these reach, d at outputs r ≥ 0 and G-almost every ε; reason: the action set is r ≥ 0 (p. 9) and the type support is [θ̲, θ̄]; no statement looks outside them, so any reading of the assumption on a domain containing this one specializes to it
--   - encoding: output R(e, θ), with E defined by R(E(r, θ), θ) = r (p. 7) → E is a primitive of the model; R does not appear; reason: the paper says the reformulated model in (r, K) "will be our focus throughout the paper", and Assumption 1 puts no condition on R
--   - reading: H(θ) = (1 − F(θ))/f(θ) decreases in θ (p. 7) → H is antitone (weakly decreasing) on [θ̲, θ̄]; reason: the proof of Proposition 1 uses only H′ ≤ 0
--   - generalization: ε has a distribution G with density g, and all functions are C³ (p. 7) → G is any probability measure on ℝ absolutely continuous w.r.t. Lebesgue measure; no smoothness of g; reason: every C³ density is such a G, so the statement specializes to the source's
--   - encoding: Θ has density f on [θ̲, θ̄]; H divides by f → f measurable, integrable on [θ̲, θ̄] with total mass 1, and f > 0 on [θ̲, θ̄]; reason: the positivity excludes only the undefined values of H
--   - encoding: D(r) = E_ε[d(r, ε)] (p. 8) → ε ↦ d(r, ε) is G-integrable for every r ≥ 0; reason: the expectation is presupposed by its definition
--   - reading: unit price p (p. 6) → p > 0; reason: a unit price; implicit in the paper
--   - encoding: partial derivatives as numbered subscripts (p. 7) → deriv of one-variable slices (pd1, pd2); reason: all functions concerned are differentiable, so the values agree
-- source:
--   Song–Lai–Xiao, Optimal Salesforce Compensation, MSOM (2024), doi:10.1287/msom.2022.0400, Appendix A, Lemma 1, p. 21

import Mathlib
import Definitions.Def_SalesforceComp_Model

open MeasureTheory

namespace SalesforceComp

open Model

/-- **Lemma 1** (signs of the output cost), Song–Lai–Xiao, *Optimal Salesforce Compensation with
General Demand and Operational Considerations*, MSOM (2024), doi:10.1287/msom.2022.0400,
Appendix A, Lemma 1, p. 21: the cost function `K(r, θ) = C(E(r, θ))` satisfies `K₁ > 0`,
`K₂ < 0`, `K₁₁ > 0`, `K₁₂ < 0`, `K₁₁₂ ≤ 0` and `K₁₂₂ ≥ 0`.

**Formalization Note.** The subscripts are the partial-derivative slices `pd1`, `pd2`
(`K₁₂ = pd2 (pd1 K)`). Assumption 1 holds at outputs `r ≥ 0` and types `θ ∈ [θ̲, θ̄]`, so the signs
hold there. -/
theorem lemma_1 (M : Model) (r θ : ℝ) (hr : 0 ≤ r) (hθ : θ ∈ M.I) :
    0 < pd1 M.K r θ ∧ pd2 M.K r θ < 0 ∧ 0 < pd1 (pd1 M.K) r θ ∧ pd2 (pd1 M.K) r θ < 0 ∧
      pd2 (pd1 (pd1 M.K)) r θ ≤ 0 ∧ 0 ≤ pd2 (pd2 (pd1 M.K)) r θ := by sorry

end SalesforceComp
