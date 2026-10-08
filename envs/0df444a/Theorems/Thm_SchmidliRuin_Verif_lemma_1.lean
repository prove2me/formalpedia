-- Prove2me | Theorems.Thm_SchmidliRuin_Verif_lemma_1
-- name    : SchmidliRuin.Verif.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:13:49.732636+00:00
-- url     : https://prove2.me/theorems/62e39af9-ba35-4a44-8c3d-4557ed8452aa
-- title:
--   Lemma 1, p. 892 — for any strategy, almost surely either ruin occurs or X_t^{Ab} → ∞
-- statement:
--   Assume the model of §1 with the standing assumptions on $c$, $\mu$, $\sigma$, the claim law and the reinsurance premium $c(b)$. Let $(A,b)$ be an arbitrary admissible strategy from initial capital $u\ge0$, with surplus process $X=X^{Ab}$. Then almost surely
--   $$\exists\,t\ge0:\ X_t<0\qquad\text{or}\qquad X_t\to\infty\ \ (t\to\infty).$$
--
--   In words: with probability one either ruin occurs or the surplus diverges to infinity. The verification theorem uses this to pass to the limit $t\to\infty$ in $\mathbb E[f(X_{t\wedge\tau})]$.
-- source:
--   Schmidli, On minimizing the ruin probability by investment and reinsurance, Ann. Appl. Probab. 12 (2002), p. 892, Lemma 1

import Mathlib
import Definitions.Def_SchmidliRuin_Verif_Setting
import Definitions.Def_SchmidliRuin_Verif_Model

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace SchmidliRuin.Verif

theorem lemma_1 {Ω : Type*} [MeasurableSpace Ω] (B : RiskBasis Ω) (hB : B.IsValid)
    (c mu sigma : ℝ) (hc : 0 < c) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (cb : ℝ → ℝ) (hcb : ReinsPremium c cb)
    (u : ℝ) (hu : 0 ≤ u) (A b X : ℝ≥0 → Ω → ℝ)
    (hadm : IsAdmissible B c mu sigma cb u A b X) :
    ∀ᵐ ω ∂B.P, (∃ t, X t ω < 0) ∨ Tendsto (fun t => X t ω) atTop atTop := by sorry

end SchmidliRuin.Verif
