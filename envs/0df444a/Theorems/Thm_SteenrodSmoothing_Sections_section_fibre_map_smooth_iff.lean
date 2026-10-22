-- Prove2me | Theorems.Thm_SteenrodSmoothing_Sections_section_fibre_map_smooth_iff
-- name    : SteenrodSmoothing.Sections.section_fibre_map_smooth_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:35:05.995729+00:00
-- url     : https://prove2.me/theorems/286db31f-a08f-457d-a394-83290d67447a
-- title:
--   Proof of Theorem 0.11, p. 5 — over a smooth trivialisation, a section is smooth near x iff its fibre part pr₂ ∘ ϕ ∘ σ′ is
-- statement:
--   Let $M$ be a finite-dimensional Hausdorff paracompact manifold with corners, $N$ a Hausdorff manifold modelled on a real normed space $F$, $E$ a manifold with corners, and $\pi : E \to M$ a map. Let $\varphi : \pi^{-1}(S) \to S \times N$ be a smooth local trivialisation of $\pi$ over the open set $S \subseteq M$ (a diffeomorphism with $\mathrm{pr}_1 \circ \varphi = \pi$). Let $\sigma' : M \to E$ be a map which is continuous on $S$ and a section over $S$, i.e. $\pi(\sigma'(y)) = y$ for $y \in S$, and put
--   $$H(\sigma') := \mathrm{pr}_2 \circ \varphi \circ \sigma' : S \to N .$$
--   Then for every $x \in S$: $\sigma'$ is smooth on a neighbourhood of $x$ if and only if $H(\sigma')$ is smooth on a neighbourhood of $x$.
--
--   In the proof of the generalised Steenrod approximation theorem this identifies sections over a trivialising set with maps into the fibre $N$, so that the relative smoothing Lemma 0.10 for maps into $N$ can be applied to sections.
--
--   **Formalization Note** The paper states this for the restricted bundle over the trivialising set $V_a$ and for continuous sections; here the section is a map $M \to E$ continuous on the base set $S$ of the trivialisation and a section over $S$, and only the smoothness equivalence is stated (not that $H$ is a homeomorphism of section spaces). "Smooth on a neighbourhood of $x$" is $C^\infty$ on an open set containing $x$. Models of $N$ and $E$ are normed spaces (the paper allows locally convex spaces); the model with corners of $M$ may be any finite-dimensional Mathlib model with corners.
-- source:
--   Wockel, A Generalisation of Steenrod's Approximation Theorem, arXiv:math/0610252v1, p. 5, proof of Theorem 0.11 ('This shows in particular that H(σ′) is smooth in a neighbourhood of x ∈ Va if and only if σ′ is so')

import Mathlib
import Definitions.Def_SteenrodSmoothing_Sections_Setting

open scoped ContDiff Manifold Topology

namespace SteenrodSmoothing.Sections

theorem section_fibre_map_smooth_iff
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
    {HM : Type*} [TopologicalSpace HM] (I : ModelWithCorners ℝ EM HM)
    {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold I ∞ M]
    [T2Space M] [ParacompactSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {N : Type*} [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N] [T2Space N]
    {EE : Type*} [NormedAddCommGroup EE] [NormedSpace ℝ EE]
    {HE : Type*} [TopologicalSpace HE] (IE : ModelWithCorners ℝ EE HE)
    {E : Type*} [TopologicalSpace E] [ChartedSpace HE E] [IsManifold IE ∞ E]
    (π : E → M) (e : Bundle.Trivialization N π) (he : IsSmoothTrivialization I F IE e)
    (s : M → E) (hsc : ContinuousOn s e.baseSet) (hs : ∀ y ∈ e.baseSet, π (s y) = y) (x : M) (hx : x ∈ e.baseSet) :
    SmoothNear I IE s {x} ↔ SmoothNear I 𝓘(ℝ, F) (fun y => (e (s y)).2) {x} := by sorry

end SteenrodSmoothing.Sections
