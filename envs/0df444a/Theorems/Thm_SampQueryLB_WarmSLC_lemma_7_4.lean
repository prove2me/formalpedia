-- Prove2me | Theorems.Thm_SampQueryLB_WarmSLC_lemma_7_4
-- name    : SampQueryLB.WarmSLC.lemma_7_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:17:29.963017+00:00
-- url     : https://prove2.me/theorems/a0eaef39-5896-4746-ae80-eec18ec7d490
-- title:
--   Lemma 7.4 — a uniform hidden direction separates nearby shell points across the 9/20 and 7/25 slabs with probability ≤ 256ρ²
-- statement:
--   Let $x,y\in\mathbb R^n$ satisfy $\|x\|,\|y\|\in[0.75,0.9]\sqrt n$ and
--   $$\min\Big\{\Big\|\frac x{\|x\|}-\frac y{\|y\|}\Big\|,\Big\|\frac x{\|x\|}+\frac y{\|y\|}\Big\|\Big\}\le\rho,\qquad0<\rho\le\frac14.$$
--
--   **Lemma 7.4.** For $v$ uniform on $S^{n-1}$,
--   $$\Pr_v\Big\{|v^\top x|>\tfrac9{20},\ |v^\top y|\le\tfrac7{25}\Big\}\le256\rho^2.$$
--
--   An output close in direction to the initial sample rarely moves from outside the wide slab into the narrow one.
--
--   **Formalization Note.** The uniform law on $S^{n-1}$ is the normalized surface measure (`sphereUnif n`, from `Measure.toSphere`).
--
--   Differences from the source:
--   - encoding: uniform v ∈ S^{n−1}; Pr_v → sphereUnif n = volume.toSphere conditioned on the whole sphere; the measure of the set of such v; reason: the normalized surface measure is the uniform law; the set is measurable
-- source:
--   Zhou, Suzuki, Towards the Query Complexity of Sampling under Strong Log-Concavity and Log-Sobolev Inequalities, arXiv:2611.05813 (held version dated November 3, 2026, sha256 966f8fc0…184c), p. 58, Lemma 7.4 (PDF p. 61)

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_SampQueryLB_WarmSLC_Model
import Definitions.Def_SampQueryLB_WarmSLC_HardFamily
import Definitions.Def_SampQueryLB_WarmSLC_Experiments

open MeasureTheory OAI.LogConcaveSampling ProbabilityTheory Filter
open scoped ENNReal ContDiff RealInnerProductSpace Topology

namespace SampQueryLB.WarmSLC

theorem lemma_7_4 (n : ℕ) (x y : Point n)
    (hx : 0.75 * Real.sqrt n ≤ ‖x‖ ∧ ‖x‖ ≤ 0.9 * Real.sqrt n)
    (hy : 0.75 * Real.sqrt n ≤ ‖y‖ ∧ ‖y‖ ≤ 0.9 * Real.sqrt n)
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 4)
    (hclose : min ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ ‖‖x‖⁻¹ • x + ‖y‖⁻¹ • y‖ ≤ ρ) :
    sphereUnif n {v | 9 / 20 < |⟪(v : Point n), x⟫| ∧ |⟪(v : Point n), y⟫| ≤ 7 / 25} ≤
      ENNReal.ofReal (256 * ρ ^ 2) := by sorry

end SampQueryLB.WarmSLC
