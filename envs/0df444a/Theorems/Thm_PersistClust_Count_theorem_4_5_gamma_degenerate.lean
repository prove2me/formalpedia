-- Prove2me | Theorems.Thm_PersistClust_Count_theorem_4_5_gamma_degenerate
-- name    : PersistClust.Count.theorem_4_5_gamma_degenerate
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T16:25:12.069993+00:00
-- url     : https://prove2.me/theorems/f29472d4-771f-4a14-b097-3576dbdcef2f
-- title:
--   Theorem 4.5 gamma-construction — degenerate case (empty superlevel)
-- statement:
--   The degenerate (empty-superlevel) case of the gamma-construction in the proof of Theorem 4.5. Given the setting of Theorem 4.5 — a complete Riemannian manifold X with positive convexity radius, a c-Lipschitz tame density f, a finite sample set L, and a scale delta small relative to the convexity radius, such that L is a delta/4-geodesic-sample of the alpha-superlevel set of f — under the additional hypothesis hvac that no point x of X satisfies alpha <= f x (the alpha-superlevel set is empty), there exists an equivalence gamma between the Copies structure of the sublevel-set diagram of f and the Copies structure of the Rips diagram of the finite sample at scale delta, which satisfies the interleaving-in-values conditions SatisfiesIIV gamma alpha (c*delta). All diagram multiplicities vanish strictly above alpha, so the off-diagonal interleaving clauses are vacuous; diagonal copies strictly above alpha are fixed by gamma; the countable diagonal bulk below alpha is routed by a Hilbert-hotel shuffle; the remaining QNE clauses hold by reflexive closeness and the QSE clauses are contradictory for diagonal points.
-- source:
--   The degenerate branch of the gamma-construction in the proof of Theorem 4.5, Persistence-Based Clustering in Riemannian Manifolds (rr/6968). Child of theorem_4_5 (id 8476e8c8-3232-437b-939f-4ea37c366d80); sibling of the accepted theorem_4_5_interleaving_corrected (whose proved finiteness output this lemma reuses) and of the matching-gate chain. This branch also closes the degenerate stub of the gamma-glue rehearsal feeding theorem_4_8_corrected (id 6b9ad4c5-ed11-4695-b810-2a1269327d27); the non-degenerate branch is the matching gate itself (currently SKETCH_ACCEPTED).

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips
import Theorems.Thm_PersistClust_Count_theorem_4_5_interleaving_corrected

open PersistClust.Count
open Bundle
open scoped ContDiff Manifold ENNReal

namespace PersistClust.Count

theorem theorem_4_5_gamma_degenerate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {X : Type*} [MetricSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
    [RiemannianBundle (fun x : X ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : X ↦ TangentSpace I x)]
    [IsRiemannianManifold I X]
    (hconv : 0 < convexityRadius X)
    (L : Finset X) (f : X → ℝ) (c : ℝ) (hc : 0 ≤ c) (hLip : ∀ x y, |f x - f y| ≤ c * dist x y)
    (htame : IsTame0 f)
    (δ : ℝ) (hδ : 0 < δ) (hδρ : ENNReal.ofReal δ < convexityRadius X)
    (α : ℝ) (hL : IsGeodesicSample (L : Set X) (superlevel f α) (δ / 4))
    (hvac : ¬ ∃ x : X, α ≤ f x) :
    ∃ γ : Copies (diagram0 f) ≃
        Copies (ripsDiagram (fun x y : L => dist (x : X) (y : X)) (fun x : L => f x) δ),
      SatisfiesIIV γ α (c * δ)
    := by sorry
