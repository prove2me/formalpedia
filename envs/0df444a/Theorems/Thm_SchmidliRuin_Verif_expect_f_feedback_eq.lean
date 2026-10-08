-- Prove2me | Theorems.Thm_SchmidliRuin_Verif_expect_f_feedback_eq
-- name    : SchmidliRuin.Verif.expect_f_feedback_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:12:35.683268+00:00
-- url     : https://prove2.me/theorems/72918345-7921-406c-8870-e91265f5cac4
-- title:
--   §3, proof of Theorem 1, p. 896 — along the feedback strategy, E[f(X*_{τ*∧t})] = f(u)
-- statement:
--   Assume the model of §1 and the standing assumptions. Let $f$ satisfy the hypotheses of Theorem 1: $f=0$ on $(-\infty,0)$, $f\ge0$, strictly increasing and continuous on $[0,\infty)$, $C^2$ on $(0,\infty)$, and solving the HJB equation (1) at every $u>0$. Let $b^*$ be a measurable maximiser of the HJB bracket in $b$, and let $(A,b,X)$ be an admissible strategy from $u>0$ that follows the feedback rule $A_t=A^*(X_{t-})$, $b_t=b^*(X_{t-})$ with $A^*$ of (2). Then, with $\tau$ the ruin time, for every $t\ge0$
--   $$\mathbb E\big[f(X_{\tau\wedge t})\big]=f(u).$$
--
--   This is the martingale identity for the candidate optimal strategy in the verification argument.
--
--   **Formalization Note** The expectation is a lower Lebesgue integral of the nonnegative random variable $f(X_{\tau\wedge t})$, so the identity also asserts its finiteness. Overshoots below $0$ contribute $0$ because $f=0$ on $(-\infty,0)$.
-- source:
--   Schmidli, On minimizing the ruin probability by investment and reinsurance, Ann. Appl. Probab. 12 (2002), p. 896, §3, proof of Theorem 1

import Mathlib
import Definitions.Def_SchmidliRuin_Verif_Setting
import Definitions.Def_SchmidliRuin_Verif_Model

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace SchmidliRuin.Verif

theorem expect_f_feedback_eq {Ω : Type*} [MeasurableSpace Ω] (B : RiskBasis Ω)
    (hB : B.IsValid) (c mu sigma : ℝ) (hc : 0 < c) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (cb : ℝ → ℝ) (hcb : ReinsPremium c cb)
    (f : ℝ → ℝ) (hf : IsHJBSolution c B.lam mu sigma cb B.ν f)
    (bstar : ℝ → ℝ) (hbstar : IsBStar c B.lam cb B.ν f bstar)
    (u : ℝ) (hu : 0 < u) (A b X : ℝ≥0 → Ω → ℝ)
    (hadm : IsAdmissible B c mu sigma cb u A b X)
    (hfb : FollowsFeedback mu sigma f bstar u A b X) (t : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (f (stopped X t ω)) ∂B.P = ENNReal.ofReal (f u) := by sorry

end SchmidliRuin.Verif
