-- Prove2me | Theorems.Thm_SchmidliRuin_Verif_expect_f_stopped_le
-- name    : SchmidliRuin.Verif.expect_f_stopped_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:12:49.048616+00:00
-- url     : https://prove2.me/theorems/bd4cfc39-fdca-4c14-be82-af6c9bace378
-- title:
--   §3, proof of Theorem 1, p. 897 — for every admissible strategy, E[f(X_{t∧τ})] ≤ f(u)
-- statement:
--   Assume the model of §1 and the standing assumptions, and let $f$ satisfy the hypotheses of Theorem 1 ($f=0$ on $(-\infty,0)$, $f\ge0$, strictly increasing and continuous on $[0,\infty)$, $C^2$ on $(0,\infty)$, solving (1) at every $u>0$). For every admissible strategy $(A,b)$ from initial capital $u\ge0$, with surplus $X$ and ruin time $\tau$, and every $t\ge0$,
--   $$\mathbb E\big[f(X_{t\wedge\tau})\big]\le f(u).$$
--
--   This is the supermartingale inequality of the verification argument: no strategy can do better than $f$.
--
--   **Formalization Note** The expectation is the lower Lebesgue integral of the nonnegative random variable $f(X_{t\wedge\tau})$, so the inequality is not satisfied by a default value when $f(X_{t\wedge\tau})$ fails to be integrable.
-- source:
--   Schmidli, On minimizing the ruin probability by investment and reinsurance, Ann. Appl. Probab. 12 (2002), p. 897, §3, proof of Theorem 1

import Mathlib
import Definitions.Def_SchmidliRuin_Verif_Setting
import Definitions.Def_SchmidliRuin_Verif_Model

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace SchmidliRuin.Verif

theorem expect_f_stopped_le {Ω : Type*} [MeasurableSpace Ω] (B : RiskBasis Ω)
    (hB : B.IsValid) (c mu sigma : ℝ) (hc : 0 < c) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (cb : ℝ → ℝ) (hcb : ReinsPremium c cb)
    (f : ℝ → ℝ) (hf : IsHJBSolution c B.lam mu sigma cb B.ν f)
    (u : ℝ) (hu : 0 ≤ u) (A b X : ℝ≥0 → Ω → ℝ)
    (hadm : IsAdmissible B c mu sigma cb u A b X) (t : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (f (stopped X t ω)) ∂B.P ≤ ENNReal.ofReal (f u) := by sorry

end SchmidliRuin.Verif
