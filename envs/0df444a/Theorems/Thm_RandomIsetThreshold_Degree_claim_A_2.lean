-- Prove2me | Theorems.Thm_RandomIsetThreshold_Degree_claim_A_2
-- name    : RandomIsetThreshold.Degree.claim_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:11:07.677027+00:00
-- url     : https://prove2.me/theorems/59d96bb9-4f44-4014-b625-d86a11badb15
-- title:
--   Claim A.2 — influence bounds noise sensitivity
-- statement:
--   For an integer $r\ge2$ and $0<p<1$, let $f$ be any measurable real-vector random output with an arbitrary independent probability seed. For every $\tau\in[0,1]$,
--
--   $$\operatorname{NS}_\tau(f)\le2\tau\,\mathcal I(f).$$
--
--   This holds with extended nonnegative quantities, including infinite influence. At $\tau=0$ both sides are zero, since resampling changes no bit. It supplies the influence-to-noise implication of Remark 1.6.
--
--   Differences from the source:
--   - encoding: vertices [n], all unordered r-sets, and real edge probabilities → Fin n, the subtype of r-element finsets, and unitInterval parameters; reason: order-preserving relabeling; interior biases are imposed or follow from the source regime
--   - encoding: independent random seeds and nonnegative expectations → an arbitrary measurable probability space, product sampling, seedwise measurability, and ENNReal moments; reason: the standing measurability convention makes probabilities meaningful; infinite moments retain their value
-- source:
--   Matthew Cho, Lutz Warnke, STOC 2027 submission #260 (October 2026), p. 23, Claim A.2

import Mathlib
import Definitions.Def_RandomIsetThreshold_Degree_RandomOutput

open MeasureTheory
open scoped ENNReal BigOperators
universe u_claim_A_2

namespace RandomIsetThreshold.Degree

theorem claim_A_2
(n r : ℕ) (hr : 2 ≤ r) (p τ : unitInterval) (hp : 0 < (p : ℝ) ∧ (p : ℝ) < 1)
    {Ω : Type u_claim_A_2} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Cube n r → Ω → Vector n) (hf : SeedMeasurable f) :
    noiseSensitivity p τ μ f ≤ ENNReal.ofReal (2 * (τ : ℝ)) * influence p μ f := by sorry

end RandomIsetThreshold.Degree
