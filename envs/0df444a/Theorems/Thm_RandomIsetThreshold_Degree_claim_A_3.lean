-- Prove2me | Theorems.Thm_RandomIsetThreshold_Degree_claim_A_3
-- name    : RandomIsetThreshold.Degree.claim_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:10:45.504696+00:00
-- url     : https://prove2.me/theorems/b8fe25f1-a079-4470-a13a-82670fc2b4b5
-- title:
--   Claim A.3 — comparison between noise rates
-- statement:
--   For an integer $r\ge2$ and $0<p<1$, let $f$ be any measurable random real-vector function of $H_{n,p}$ and an arbitrary independent probability seed. For every $\tau,t\in(0,1]$,
--
--   $$\operatorname{NS}_\tau(f)\le\max\{\tau/t,1\}\operatorname{NS}_t(f).$$
--
--   The comparison applies even if one or both sensitivities are infinite. It allows a stability assumption at one rate to control another rate.
--
--   Differences from the source:
--   - encoding: vertices [n], all unordered r-sets, and real edge probabilities → Fin n, the subtype of r-element finsets, and unitInterval parameters; reason: order-preserving relabeling; interior biases are imposed or follow from the source regime
--   - encoding: independent random seeds and nonnegative expectations → an arbitrary measurable probability space, product sampling, seedwise measurability, and ENNReal moments; reason: the standing measurability convention makes probabilities meaningful; infinite moments retain their value
-- source:
--   Matthew Cho, Lutz Warnke, STOC 2027 submission #260 (October 2026), p. 23, Claim A.3

import Mathlib
import Definitions.Def_RandomIsetThreshold_Degree_RandomOutput

open MeasureTheory
open scoped ENNReal BigOperators
universe u_claim_A_3

namespace RandomIsetThreshold.Degree

theorem claim_A_3
(n r : ℕ) (hr : 2 ≤ r) (p τ t : unitInterval) (hp : 0 < (p : ℝ) ∧ (p : ℝ) < 1)
    (hτ : 0 < (τ : ℝ)) (ht : 0 < (t : ℝ))
    {Ω : Type u_claim_A_3} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Cube n r → Ω → Vector n) (hf : SeedMeasurable f) :
    noiseSensitivity p τ μ f ≤ ENNReal.ofReal (max ((τ : ℝ) / (t : ℝ)) 1) *
      noiseSensitivity p t μ f := by sorry

end RandomIsetThreshold.Degree
