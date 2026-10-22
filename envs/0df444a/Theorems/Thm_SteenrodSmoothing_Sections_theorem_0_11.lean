-- Prove2me | Theorems.Thm_SteenrodSmoothing_Sections_theorem_0_11
-- name    : SteenrodSmoothing.Sections.theorem_0_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:35:06.119153+00:00
-- url     : https://prove2.me/theorems/e71707e6-eb0a-46ac-b71a-9553dfc4e8f5
-- title:
--   Theorem 0.11, p. 4 — Generalised Steenrod Approximation: a continuous section smooth near L ∖ U is homotopic in O, fixed off U, to a section smooth near L
-- statement:
--   **Generalised Steenrod Approximation Theorem.** Let $M$ be a finite-dimensional connected manifold with corners (Hausdorff and paracompact), let $N$ be a Hausdorff smooth manifold modelled on a real normed space $F$, and let $\pi : E \to M$ be a locally trivial smooth bundle with typical fibre $N$. Let $\sigma : M \to E$ be a continuous section, $\pi \circ \sigma = \mathrm{id}_M$. Let $L \subseteq M$ be closed and $U \subseteq M$ open, and assume that $\sigma$ is smooth on a neighbourhood of $L \setminus U$. Then for each open set $O \subseteq E$ with $\sigma(M) \subseteq O$ there exist
--
--   1. a continuous section $\tau : M \to E$ with $\tau(M) \subseteq O$, which is smooth on a neighbourhood of $L$ and satisfies $\tau(x) = \sigma(x)$ for $x \in M \setminus U$, and
--   2. a continuous homotopy $H : [0,1] \times M \to O$ from $\sigma$ to $\tau$ through sections, fixed off $U$:
--   $$H(0, \cdot) = \sigma,\quad H(1,\cdot) = \tau,\quad \pi(H(t,x)) = x,\quad H(t, x) = \sigma(x) = \tau(x) \ \text{ for } (t,x) \in [0,1] \times (M \setminus U).$$
--
--   This extends Steenrod's smoothing of sections (Steenrod 1951, §6.7) to bundles whose typical fibre may be infinite-dimensional. Its consequences in the paper are the density of smooth maps $M \to N$ in the graph and compact-open topologies (Corollary 0.12) and the agreement of smooth and continuous homotopy classes of sections and maps (Proposition 0.13, Corollary 0.14).
--
--   **Formalization Note** The paper allows $N$ to be modelled on an arbitrary locally convex space; here $N$ and the total space $E$ are modelled on real normed spaces (not necessarily complete), where the paper's smoothness coincides with Mathlib's $C^\infty$. "Paracompact Hausdorff" comes from Definition 0.3 and "Hausdorff" for $N$ from Definition 0.1; $E$ may have corners. The model with corners of $M$ may be any finite-dimensional Mathlib model with corners, which contains the paper's quadrant $\mathbb R^d_+$. "Smooth on a neighbourhood of a set" means $C^\infty$ on an open set containing it. The homotopy is called $H$ (the letter $F$ denotes the model space of $N$) and runs from $\sigma$ at $t = 0$ to $\tau$ at $t = 1$; the paper's proof parametrises it the other way, which is the same statement after $t \mapsto 1 - t$.
-- source:
--   Wockel, A Generalisation of Steenrod's Approximation Theorem, arXiv:math/0610252v1, p. 4, Theorem 0.11 (with Definitions 0.1, 0.3, p. 2)

import Mathlib
import Definitions.Def_SteenrodSmoothing_Sections_Setting

open scoped ContDiff Manifold Topology

namespace SteenrodSmoothing.Sections

theorem theorem_0_11
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
    {HM : Type*} [TopologicalSpace HM] (I : ModelWithCorners ℝ EM HM)
    {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold I ∞ M]
    [T2Space M] [ParacompactSpace M] [ConnectedSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (N : Type*) [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N] [T2Space N]
    {EE : Type*} [NormedAddCommGroup EE] [NormedSpace ℝ EE]
    {HE : Type*} [TopologicalSpace HE] (IE : ModelWithCorners ℝ EE HE)
    {E : Type*} [TopologicalSpace E] [ChartedSpace HE E] [IsManifold IE ∞ E]
    (π : E → M) (hπ : IsSmoothLocallyTrivialBundle I F N IE π)
    (σ : M → E) (hσ : Continuous σ) (hσπ : ∀ x, π (σ x) = x)
    (L U : Set M) (hL : IsClosed L) (hU : IsOpen U) (hσL : SmoothNear I IE σ (L \ U))
    (O : Set E) (hO : IsOpen O) (hσO : Set.range σ ⊆ O) :
    ∃ τ : M → E, Continuous τ ∧ (∀ x, π (τ x) = x) ∧ Set.range τ ⊆ O ∧
      SmoothNear I IE τ L ∧ (∀ x, x ∉ U → τ x = σ x) ∧
      ∃ H : unitInterval × M → E, Continuous H ∧
        (∀ x, H (0, x) = σ x) ∧ (∀ x, H (1, x) = τ x) ∧
        (∀ p, H p ∈ O) ∧ (∀ p, π (H p) = p.2) ∧
        (∀ t x, x ∉ U → H (t, x) = σ x) := by sorry

end SteenrodSmoothing.Sections
