-- Prove2me | Theorems.Thm_SchmidliRuin_Verif_feedback_no_creeping
-- name    : SchmidliRuin.Verif.feedback_no_creeping
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:12:41.08773+00:00
-- url     : https://prove2.me/theorems/2e1a2597-30f0-4d6c-aaa5-dd3c6f9fa11d
-- title:
--   §3, proof of Theorem 1, p. 897 — under the feedback strategy, ℙ[τ* < ∞, X*_{τ*} = 0] = 0
-- statement:
--   Assume the model of §1 and the standing assumptions, let $f$ satisfy the hypotheses of Theorem 1 and let $b^*$ be a measurable maximiser of the HJB bracket in $b$. For every admissible strategy from $u>0$ that follows the feedback rule $A_t=A^*(X_{t-})$, $b_t=b^*(X_{t-})$, with ruin time $\tau^*$,
--   $$\mathbb P\big[\tau^*<\infty,\ X_{\tau^*}=0\big]=0 .$$
--
--   Ruin does not occur by creeping through $0$: at ruin the surplus jumps strictly below $0$. This removes the term $f(0)\,\mathbb P[\tau<\infty,X_\tau=0]$ from the limit of $\mathbb E[f(X_{t\wedge\tau})]$ and gives equality in the verification theorem.
--
--   **Formalization Note** The paper's proof chooses "$\varepsilon>0$ such that $b^*(x)=0$ for $x\le2\varepsilon$"; by Lemma 3 (and p. 898: "the optimal strategy will be $b^*(u)=1$ for $u$ small enough") this is a misprint for $b^*(x)=1$. The statement itself does not involve it.
-- source:
--   Schmidli, On minimizing the ruin probability by investment and reinsurance, Ann. Appl. Probab. 12 (2002), p. 897, §3, proof of Theorem 1

import Mathlib
import Definitions.Def_SchmidliRuin_Verif_Setting
import Definitions.Def_SchmidliRuin_Verif_Model

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace SchmidliRuin.Verif

theorem feedback_no_creeping {Ω : Type*} [MeasurableSpace Ω] (B : RiskBasis Ω)
    (hB : B.IsValid) (c mu sigma : ℝ) (hc : 0 < c) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (cb : ℝ → ℝ) (hcb : ReinsPremium c cb)
    (f : ℝ → ℝ) (hf : IsHJBSolution c B.lam mu sigma cb B.ν f)
    (bstar : ℝ → ℝ) (hbstar : IsBStar c B.lam cb B.ν f bstar)
    (u : ℝ) (hu : 0 < u) (A b X : ℝ≥0 → Ω → ℝ)
    (hadm : IsAdmissible B c mu sigma cb u A b X)
    (hfb : FollowsFeedback mu sigma f bstar u A b X) :
    B.P {ω | ruinTime X ω < ⊤ ∧ X (ruinTime X ω).toNNReal ω = 0} = 0 := by sorry

end SchmidliRuin.Verif
