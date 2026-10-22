-- Prove2me | Theorems.Thm_SteenrodSmoothing_Sections_proposition_0_7
-- name    : SteenrodSmoothing.Sections.proposition_0_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:22.442726+00:00
-- url     : https://prove2.me/theorems/48c6febf-71d1-4d72-834c-cdd0184f0247
-- title:
--   Proposition 0.7, p. 3 — smooth maps are dense in C(M, Y) with the compact-open topology, with support control
-- statement:
--   Let $M$ be a finite-dimensional σ-compact Hausdorff manifold with corners and $Y$ a real normed space. Write $C(M, Y)_{c.o.}$ for the space of continuous maps $M \to Y$ with the compact-open topology, and $\operatorname{supp}(f) = \overline{\{x : f(x) \neq 0\}}$. Then:
--
--   1. the smooth maps are dense:
--   $$\overline{C^\infty(M, Y)} = C(M, Y)_{c.o.};$$
--   2. if $f \in C(M, Y)$ has compact support and $U \subseteq M$ is open with $\operatorname{supp}(f) \subseteq U$, then every neighbourhood of $f$ in $C(M, Y)_{c.o.}$ contains a smooth map $g$ with $\operatorname{supp}(g) \subseteq U$.
--
--   This is the basic approximation result on which the relative smoothing Lemmas 0.9 and 0.10 and hence the generalised Steenrod approximation theorem rest.
--
--   **Formalization Note** The paper allows any locally convex space $Y$; here $Y$ is a real normed space (Mathlib's manifolds need normed models), where the paper's smoothness coincides with Mathlib's $C^\infty$. "Each neighbourhood of $f$ in $C(M, Y)$" is read in the compact-open topology of the first sentence (Mathlib's default topology on `C(M, Y)`), and "support" is the closed support `tsupport`. "Paracompact Hausdorff" of Definition 0.3 enters as `[T2Space M]`; paracompactness follows from σ-compactness and local compactness. The model with corners may be any finite-dimensional Mathlib model with corners.
-- source:
--   Wockel, A Generalisation of Steenrod's Approximation Theorem, arXiv:math/0610252v1, p. 3, Proposition 0.7 (with Definition 0.5)

import Mathlib

open scoped ContDiff Manifold Topology

namespace SteenrodSmoothing.Sections

theorem proposition_0_7
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
    {HM : Type*} [TopologicalSpace HM] (I : ModelWithCorners ℝ EM HM)
    {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] :
    Dense {f : C(M, Y) | ContMDiff I 𝓘(ℝ, Y) ∞ f} ∧
      ∀ f : C(M, Y), HasCompactSupport f → ∀ U : Set M, IsOpen U → tsupport f ⊆ U →
        ∀ 𝒩 ∈ 𝓝 f, ∃ g ∈ 𝒩, ContMDiff I 𝓘(ℝ, Y) ∞ g ∧ tsupport g ⊆ U := by sorry

end SteenrodSmoothing.Sections
