-- Prove2me | Theorems.Thm_SalesforceComp_proposition_1_monotone
-- name    : SalesforceComp.proposition_1_monotone
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:25:19.604432+00:00
-- url     : https://prove2.me/theorems/250b8aaf-6b01-41bf-8af4-7966c590a000
-- title:
--   Proof of Proposition 1, pp. 22–23 — (1) determines $r^*(\theta)$, and $r^*$ is strictly increasing (corrected: $Q^*$ not unique)
-- statement:
--   Work in the model of §2 with Assumption 1 (the `Model` definition of this mission): output cost $K(r,\theta)=C(E(r,\theta))$, expected demand $D$, expected sales $S$, inverse hazard rate $H$ on the type support $[\underline\theta,\bar\theta]$, and the virtual surplus $M(r,Q,\theta)=pS(r,Q)-(c+h)Q-K(r,\theta)+K_2(r,\theta)H(\theta)$.
--
--   Let $r^*,Q^*$ be functions with $r^*(\theta)\ge0$, $Q^*(\theta)\ge0$ that solve system (1),
--   $$pS_1(r,Q)-K_1(r,\theta)+K_{12}(r,\theta)H(\theta)=0,\qquad pS_2(r,Q)-c-h=0,$$
--   at every $\theta\in[\underline\theta,\bar\theta]$, and let $V^*=\mathbb E_\Theta[M(r^*(\Theta),Q^*(\Theta),\Theta)]$. Then:
--
--   1. at every $\theta\in[\underline\theta,\bar\theta]$, every solution $(x,q)$ of (1) with $x\ge0$, $q\ge0$ has $x=r^*(\theta)$;
--   2. $r^*$ is strictly increasing on $[\underline\theta,\bar\theta]$.
--
--   The second-best output is thus pinned down by (1) and rises with the market condition, which is what makes the screening of types possible.
--
--   **Formalization Note** Only the output component is unique. When the density of $\varepsilon$ vanishes at the critical fractile, (1) is solved by a whole interval of inventories, so the proof's uniqueness of $Q^*$ and its claim that $Q^*$ increases are not stated.
--
--   Differences from the source:
--   - correction: (1) uniquely determines the optimal pair (r*, Q*) (p. 22), and Q*(θ) is increasing in θ (p. 23) → only the output is unique (clause 1); r* strictly increasing (clause 2); nothing is claimed about Q*; reason: false in general: with d = r + ε, ε with density 1/2 on [−2, −1] ∪ [1, 2], C = exp, E = r − θ, Θ ~ U[1, 2], p = 8, c = 3, h = 1, every Q ∈ [r*(θ) − 1, r*(θ) + 1] solves (1) with r*(θ) = θ + ln(4/(3 − θ)), so a non-monotone selection Q* is a solution
--   - reading: the outcome (r*(θ), Q*(θ)) solves system (1) (Proposition 1, p. 9) → r*, Q* are any functions with r*(θ) ≥ 0, Q*(θ) ≥ 0 solving (1) at every θ ∈ [θ̲, θ̄]; uniqueness is not assumed; reason: the paper presupposes a solution; (1) need not determine Q* uniquely (see proposition_1_monotone)
--   - generalization: Assumption 1 (C), (D), (E), p. 7, printed without a domain → C, d, E are C³ on ℝ, ℝ², ℝ²; the sign conditions are required only on the domain of the model: E at outputs r ≥ 0 and types θ ∈ [θ̲, θ̄], C at the efforts E(r, θ) these reach, d at outputs r ≥ 0 and G-almost every ε; reason: the action set is r ≥ 0 (p. 9) and the type support is [θ̲, θ̄]; no statement looks outside them, so any reading of the assumption on a domain containing this one specializes to it
--   - encoding: output R(e, θ), with E defined by R(E(r, θ), θ) = r (p. 7) → E is a primitive of the model; R does not appear; reason: the paper says the reformulated model in (r, K) "will be our focus throughout the paper", and Assumption 1 puts no condition on R
--   - reading: H(θ) = (1 − F(θ))/f(θ) decreases in θ (p. 7) → H is antitone (weakly decreasing) on [θ̲, θ̄]; reason: the proof of Proposition 1 uses only H′ ≤ 0
--   - generalization: ε has a distribution G with density g, and all functions are C³ (p. 7) → G is any probability measure on ℝ absolutely continuous w.r.t. Lebesgue measure; no smoothness of g; reason: every C³ density is such a G, so the statement specializes to the source's
--   - encoding: Θ has density f on [θ̲, θ̄]; H divides by f → f measurable, integrable on [θ̲, θ̄] with total mass 1, and f > 0 on [θ̲, θ̄]; reason: the positivity excludes only the undefined values of H
--   - encoding: D(r) = E_ε[d(r, ε)] (p. 8) → ε ↦ d(r, ε) is G-integrable for every r ≥ 0; reason: the expectation is presupposed by its definition
--   - reading: unit price p (p. 6) → p > 0; reason: a unit price; implicit in the paper
--   - encoding: partial derivatives as numbered subscripts (p. 7) → deriv of one-variable slices (pd1, pd2); reason: all functions concerned are differentiable, so the values agree
-- source:
--   Song–Lai–Xiao, Optimal Salesforce Compensation, MSOM (2024), doi:10.1287/msom.2022.0400, Appendix A, proof of Proposition 1, pp. 22–23

import Mathlib
import Definitions.Def_SalesforceComp_Model

open MeasureTheory

namespace SalesforceComp

open Model

/-- **The second-best output is determined by (1) and strictly increasing**, Song–Lai–Xiao,
MSOM (2024), doi:10.1287/msom.2022.0400, Appendix A, proof of Proposition 1, pp. 22–23 ("its
system of first-order conditions (FOC) uniquely determines the optimal pair"; "by Topkis'
Theorem, `r*(θ)` is strictly increasing in `θ`").

Let `(r*, Q*)` be nonnegative and solve system (1) on `[θ̲, θ̄]`. Then
1. at every `θ ∈ [θ̲, θ̄]`, every nonnegative solution `(x, q)` of (1) has `x = r*(θ)`;
2. `r*` is strictly increasing on `[θ̲, θ̄]`.

**Formalization Note.** Only the output component is unique: (1) can be solved by a whole
interval of inventories `Q` when the density of `ε` vanishes at the critical fractile, so the
proof's uniqueness of `Q*` and its claim that `Q*` is increasing are not stated. -/
theorem proposition_1_monotone (M : Model) (rs Qs : ℝ → ℝ) (hsol : M.SolvesFOC rs Qs) :
    (∀ θ ∈ M.I, ∀ x q : ℝ, 0 ≤ x → 0 ≤ q → M.FOC x q θ → x = rs θ) ∧
      StrictMonoOn rs M.I := by sorry

end SalesforceComp
