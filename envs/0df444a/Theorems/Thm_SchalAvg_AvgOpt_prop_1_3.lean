-- Prove2me | Theorems.Thm_SchalAvg_AvgOpt_prop_1_3
-- name    : SchalAvg.AvgOpt.prop_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:50:57.362275+00:00
-- url     : https://prove2.me/theorems/771765bb-1bc1-4c03-8e5d-078b1e2b1e12
-- title:
--   Proposition 1.3 — a nonnegative finite solution of the average cost optimality inequality gives Φ(f₁, x) = g = g̲ = ḡ
-- statement:
--   In Schäl's decision model $(S, A, A(\cdot), q, c)$ (standard Borel spaces, costs in $[0, \infty]$) assume the General Assumption $g < \infty$. Suppose there are a measurable function $\underline w : S \to [0, \infty)$ and a stationary policy $f_1 \in \mathbb F$ satisfying the **average cost optimality inequality** with the constant $\underline g = \liminf_{\beta \to 1} (1-\beta) m_\beta$:
--   $$\underline w(x) + \underline g \ \ge\ c(x, f_1(x)) + \int \underline w \, dq(x, f_1(x)) \qquad \text{for all } x \in S.$$
--   Then for all $x \in S$,
--   $$\Phi(f_1, x) = g = \underline g = \bar g.$$
--
--   In words: a finite nonnegative solution of the optimality *inequality* (rather than the optimality equation) with the constant $\underline g$ already makes $f_1$ average optimal, and forces the vanishing-discount limit $\lim_{\beta \to 1}(1-\beta)m_\beta$ to exist and equal the optimal average cost.
--
--   **Formalization Note.** $\underline w$ is a measurable function into $[0, \infty]$ that is nowhere $\infty$ (the paper's "$\underline w : S \to [0, \infty)$"); the integral is the lower Lebesgue integral against $q(\cdot \mid x, f_1(x))$. The constant on the left is $\underline g$ (the paper's underlined $g$), not $g$. The General Assumption is the paper's standing assumption (p. 164). $\Phi(f_1, \cdot)$ is the average cost of the stationary policy $f_1$ viewed as a policy.
-- source:
--   Schäl, Average Optimality in Dynamic Programming with General State Space, Math. Oper. Res. 18(1) (1993), p. 164, Proposition 1.3

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter FeinbergLiang.ACOE

namespace SchalAvg.AvgOpt

theorem prop_1_3 {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S]
    [MeasurableSpace A] [StandardBorelSpace A] (M : Model S A) (hGA : GeneralAssumption M)
    (w : S → ℝ≥0∞) (hw_meas : Measurable w) (hw_fin : ∀ x, w x ≠ ⊤)
    (f₁ : S → A) (hf₁ : IsStationary M f₁)
    (hACOI : ∀ x, M.toMDP.cost x (f₁ x) + ∫⁻ y, w y ∂(M.toMDP.q (x, f₁ x)) ≤ w x + gLower M) :
    (∀ x, Phi M (statPolicy hf₁) x = gStar M) ∧ gStar M = gLower M ∧ gLower M = gUpper M := by sorry

end SchalAvg.AvgOpt
