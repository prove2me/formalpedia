-- Prove2me | Theorems.Thm_SchmidliRuin_Verif_survival_le_and_eq
-- name    : SchmidliRuin.Verif.survival_le_and_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:12:19.918796+00:00
-- url     : https://prove2.me/theorems/36001dd5-ffed-49d3-9dcc-cb4230d2c4a3
-- title:
--   §3, proof of Theorem 1, p. 897 — f(∞) < ∞, δ^{Ab}(u) ≤ f(u)/f(∞), with equality for the feedback strategy
-- statement:
--   Assume the model of §1 and the standing assumptions, and let $f$ satisfy the hypotheses of Theorem 1. Then $f(\infty)=\lim_{x\to\infty}f(x)$ exists as a positive real number $L$, and:
--
--   1. for every admissible strategy $(A,b)$ from $u\ge0$,
--   $$\delta^{Ab}(u)=\mathbb P[\tau=\infty]\le\frac{f(u)}{f(\infty)};$$
--   2. for every measurable maximiser $b^*$ of the HJB bracket in $b$, every $u>0$ and every admissible strategy from $u$ following the feedback rule $A_t=A^*(X_{t-})$, $b_t=b^*(X_{t-})$, equality holds: $\delta^{A^*b^*}(u)=f(u)/f(\infty)$.
--
--   This is the comparison step of the verification theorem, before the value function is identified.
--
--   **Formalization Note** The existence of the finite limit $f(\infty)$ is part of the conclusion (the paper derives it here from the existence of a strategy with positive survival probability). Equality is stated for $u>0$, as in the paper's proof, which takes $0<\varepsilon<u$.
-- source:
--   Schmidli, On minimizing the ruin probability by investment and reinsurance, Ann. Appl. Probab. 12 (2002), p. 897, §3, proof of Theorem 1

import Mathlib
import Definitions.Def_SchmidliRuin_Verif_Setting
import Definitions.Def_SchmidliRuin_Verif_Model

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace SchmidliRuin.Verif

theorem survival_le_and_eq {Ω : Type*} [MeasurableSpace Ω] (B : RiskBasis Ω)
    (hB : B.IsValid) (c mu sigma : ℝ) (hc : 0 < c) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (cb : ℝ → ℝ) (hcb : ReinsPremium c cb)
    (f : ℝ → ℝ) (hf : IsHJBSolution c B.lam mu sigma cb B.ν f) :
    ∃ L : ℝ, 0 < L ∧ Tendsto f atTop (𝓝 L) ∧
      (∀ u, 0 ≤ u → ∀ A b X : ℝ≥0 → Ω → ℝ, IsAdmissible B c mu sigma cb u A b X →
        survivalProb B X ≤ f u / L) ∧
      (∀ bstar : ℝ → ℝ, IsBStar c B.lam cb B.ν f bstar →
        ∀ u, 0 < u → ∀ A b X : ℝ≥0 → Ω → ℝ,
          IsAdmissible B c mu sigma cb u A b X → FollowsFeedback mu sigma f bstar u A b X →
          survivalProb B X = f u / L) := by sorry

end SchmidliRuin.Verif
