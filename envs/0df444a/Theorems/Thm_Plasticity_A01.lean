-- Prove2me | Theorems.Thm_Plasticity_A01
-- name    : Plasticity.A01
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T07:40:05.018599+00:00
-- url     : https://prove2.me/theorems/b6ee41d6-0736-4a3f-9b96-a7cf21b4ed0c
-- title:
--   Forward common-face rigidity: $\|a+H(a)\|=2$ on the sphere forces $H=I$
-- statement:
--   Let $X$ be a real Banach space with closed unit ball $B_X$ and unit sphere $S_X$, and let $H\colon B_X\to B_X$ be nonexpansive.
--   If $\|a+H(a)\|=2$ for every $a\in S_X$, then $H$ is the identity on $B_X$.
--   No injectivity, surjectivity or zero-fixing assumption is made on $H$.
-- source:
--   This repository: claim A01 (claims/a.md); proof in expositions/smooth/reflexivity_and_averaging.md §5, using uniform asymptotic regularity of averaged nonexpansive maps (Borzdyński–Wiśnicki, arXiv:1511.04069, Prop. 2.2, Lemma 3.1, Thm 3.3; in textbook form Goebel–Kirk, Topics in Metric Fixed Point Theory, 1990, Thm 9.4)

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity
theorem A01 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (H : X → X)
    (hmaps : Set.MapsTo H (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : X) 1))
    (hlip : LipschitzOnWith 1 H (Metric.closedBall (0 : X) 1))
    (halign : ∀ a ∈ Metric.sphere (0 : X) 1, ‖a + H a‖ = 2) :
    Set.EqOn H id (Metric.closedBall (0 : X) 1) := by sorry
end Plasticity
