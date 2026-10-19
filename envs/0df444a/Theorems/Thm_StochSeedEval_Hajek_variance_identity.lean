-- Prove2me | Theorems.Thm_StochSeedEval_Hajek_variance_identity
-- name    : StochSeedEval.Hajek.variance_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:21.656182+00:00
-- url     : https://prove2.me/theorems/3ba3811a-ac28-4c45-975e-69272aace2c6
-- title:
--   Proof of Proposition 2, p. 40 — corrected delta-method variance identity
-- statement:
--   Under full positivity and finite second moments of $w_A$, $w_B$, $w_Ay$, and $w_By$, define the centered influence variable
--
--   $$L(S)=w_A(S)(y(S)-\mu_A)-w_B(S)(y(S)-\mu_B).$$
--
--   It has design expectation zero and variance equal to equation (15):
--
--   $$\mathbb E_\Delta[L]=0,\qquad \operatorname{Var}_\Delta(L)=V_{\widetilde\tau}=\mathbb E_\Delta\left[\left(\frac{\mu_Ap_A-\mu_Bp_B-y(p_A-p_B)}{p_\Delta}\right)^2\right].$$
--
--   This pins the limit variance to the strategies, design, and outcome, including the dependence between the two weighted terms.
--
--   **Formalization Note.** The paper's intermediate expansion on p. 40 has a wrong sign in one cross term; the final expression (15) is the stated variance.
-- source:
--   Chin, Eckles & Ugander, Evaluating Stochastic Seeding Strategies in Networks, arXiv:1809.09561v3, p. 40, proof of Proposition 2, delta-method variance display and equation (15) (corrected intermediate signs)

import Mathlib
import Definitions.Def_StochSeedEval_Hajek_Estimators

open MeasureTheory ProbabilityTheory

namespace StochSeedEval.Hajek

/-- Corrected delta-method variance identity, proof of Proposition 2, p. 40. -/
theorem variance_identity
    {Ω : Type*} [Countable Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (pA pB pD : PMF Ω) (y : Ω → ℝ)
    (hpos : ∀ s, (pA s ≠ 0 ∨ pB s ≠ 0) → pD s ≠ 0)
    (hA2 : MemLp (weightA pA pD) 2 pD.toMeasure)
    (hB2 : MemLp (weightB pB pD) 2 pD.toMeasure)
    (hAy2 : MemLp (fun s => weightA pA pD s * y s) 2 pD.toMeasure)
    (hBy2 : MemLp (fun s => weightB pB pD s * y s) 2 pD.toMeasure) :
    (∫ s, influence pA pB pD y s ∂pD.toMeasure) = 0 ∧
    variance (influence pA pB pD y) pD.toMeasure = asymptoticVariance pA pB pD y := by sorry

end StochSeedEval.Hajek
