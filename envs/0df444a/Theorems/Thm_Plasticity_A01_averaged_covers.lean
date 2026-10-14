-- Prove2me | Theorems.Thm_Plasticity_A01_averaged_covers
-- name    : Plasticity.A01.averaged_covers
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T07:54:18.231163+00:00
-- url     : https://prove2.me/theorems/1b28e098-5435-4ffc-b9b4-61f26270d8d9
-- title:
--   A small average of a ball self-map that nearly preserves the sphere covers a concentric ball
-- statement:
--   Let $X$ be a real Banach space and $K\colon B_X\to B_X$ nonexpansive. Let $0<\alpha<\tfrac14$ and $0\le d<1$, and put $P=(1-\alpha)I+\alpha K$.
--   If
--   $$\|P(a)\|\ge1-d\qquad(a\in S_X),$$
--   then every $y\in X$ with $\|y\|\le1-d$ is $P(x)$ for some $x\in B_X$; that is, $(1-d)B_X\subseteq P(B_X)$.
--
--   With $d=0$ this says that $P$ maps $B_X$ onto $B_X$, the step of A01 that makes the published uniform asymptotic regularity applicable; with $d>0$ it is the covering step (2.3) of the quantitative form.
--
--   **Formalization Note** The proof extends $K$ radially to a $3$-Lipschitz map of $X$ and solves $P(x)=y$ by the contraction principle; the statement does not mention the extension.
-- source:
--   This repository: expositions/smooth/reflexivity_and_averaging.md §5, radial extension (5.2)–(5.3) and the proof of Lemma C up to P(B_V)=B_V; quantitative form expositions/universal/conjugated_contractions.md §2.1, (2.3)

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.A01
theorem averaged_covers {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (K : X → X)
    (hmaps : Set.MapsTo K (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : X) 1))
    (hlip : LipschitzOnWith 1 K (Metric.closedBall (0 : X) 1))
    (α d : ℝ) (hα0 : 0 < α) (hα1 : α < 1 / 4) (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hd : ∀ a ∈ Metric.sphere (0 : X) 1, 1 - d ≤ ‖(1 - α) • a + α • K a‖)
    (y : X) (hy : ‖y‖ ≤ 1 - d) :
    ∃ x ∈ Metric.closedBall (0 : X) 1, (1 - α) • x + α • K x = y := by sorry
end Plasticity.A01
