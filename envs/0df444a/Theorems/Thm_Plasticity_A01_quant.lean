-- Prove2me | Theorems.Thm_Plasticity_A01_quant
-- name    : Plasticity.A01_quant
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T07:40:14.443127+00:00
-- url     : https://prove2.me/theorems/c93402b5-174f-4a0d-921d-6576eca38227
-- title:
--   Quantitative common-face rigidity: $\|H-I\|_\infty\le\min\{2,4\varepsilon^{1/3}\}$
-- statement:
--   Let $X$ be a real Banach space with closed unit ball $B_X$ and unit sphere $S_X$, let $\varepsilon\ge0$, and let $H\colon B_X\to B_X$ be $(1+\varepsilon)$-Lipschitz.
--   If $\|a+H(a)\|=2$ for every $a\in S_X$, then
--   $$\sup_{x\in B_X}\|H(x)-x\|\le\min\{2,\,4\varepsilon^{1/3}\}.$$
--   For $\varepsilon=0$ this is the exact form (card Plasticity.A01). No injectivity or surjectivity of $H$ is assumed.
-- source:
--   This repository: claim A01 (claims/a.md), displayed quantitative form; proof in expositions/universal/conjugated_contractions.md §2 (Lemma 2.1), using the rate sup‖Pⁿx−K(Pⁿx)‖ ≤ 2/√(πnα(1−α)) for averaged nonexpansive maps (Cominetti–Soto–Vaisman, arXiv:1206.4195, Theorem 1)

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity
theorem A01_quant {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (ε : NNReal) (H : X → X)
    (hmaps : Set.MapsTo H (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : X) 1))
    (hlip : LipschitzOnWith (1 + ε) H (Metric.closedBall (0 : X) 1))
    (halign : ∀ a ∈ Metric.sphere (0 : X) 1, ‖a + H a‖ = 2) :
    ∀ x ∈ Metric.closedBall (0 : X) 1, ‖H x - x‖ ≤ min 2 (4 * (ε : ℝ) ^ ((1 : ℝ) / 3)) := by sorry
end Plasticity
