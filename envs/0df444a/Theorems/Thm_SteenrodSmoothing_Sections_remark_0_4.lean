-- Prove2me | Theorems.Thm_SteenrodSmoothing_Sections_remark_0_4
-- name    : SteenrodSmoothing.Sections.remark_0_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:21.4439+00:00
-- url     : https://prove2.me/theorems/f7f39589-da65-41e8-b535-4fd57f9e8611
-- title:
--   Remark 0.4, p. 3 — a connected paracompact Hausdorff finite-dimensional manifold with corners is σ-compact
-- statement:
--   Let $M$ be a finite-dimensional manifold with corners (modelled by a model with corners $I$ on a finite-dimensional real normed space, with smooth coordinate changes) which is Hausdorff, paracompact and connected. Then $M$ is σ-compact:
--   $$M = \bigcup_{n \in \mathbb N} K_n \quad\text{with each } K_n \subseteq M \text{ compact}.$$
--
--   This is the direction of Remark 0.4 (via Dugundji, Theorems XI.7.2–3) used in the proof of the generalised Steenrod approximation theorem: a locally compact paracompact space has σ-compact components, so a connected one is σ-compact (equivalently Lindelöf). It lets the proof of Theorem 0.11 index its locally finite covers by $\mathbb N$ and apply Lemma 0.10, which assumes σ-compactness.
--
--   **Formalization Note** Only the direction "paracompact and connected ⇒ σ-compact" is stated, not the full equivalence "paracompact ⇔ each component σ-compact" of the remark. "Paracompact Hausdorff" is part of Definition 0.3 of a manifold with corners. The model with corners $I$ may be any finite-dimensional Mathlib model with corners, which contains the paper's quadrant $\mathbb R^d_+$.
-- source:
--   Wockel, A Generalisation of Steenrod's Approximation Theorem, arXiv:math/0610252v1, p. 3, Remark 0.4 (second paragraph), with Definition 0.3, p. 2

import Mathlib

open scoped ContDiff Manifold Topology

namespace SteenrodSmoothing.Sections

theorem remark_0_4
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
    {HM : Type*} [TopologicalSpace HM] (I : ModelWithCorners ℝ EM HM)
    {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold I ∞ M]
    [T2Space M] [ParacompactSpace M] [ConnectedSpace M] :
    SigmaCompactSpace M := by sorry

end SteenrodSmoothing.Sections
