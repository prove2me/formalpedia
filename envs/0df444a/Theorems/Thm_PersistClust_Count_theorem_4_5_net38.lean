-- Prove2me | Theorems.Thm_PersistClust_Count_theorem_4_5_net38
-- name    : PersistClust.Count.theorem_4_5_net38
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-16T05:30:25.661834+00:00
-- url     : https://prove2.me/theorems/f8b60f13-169d-4577-9e90-db98212c9d39
-- title:
--   Theorem 4.5 from a geodesic 3δ/8-sample: the multi-bijection D₀f ≃ D₀𝓡^f_δ(L) with guarantees (i)–(iv) at radius cδ
-- statement:
--   Variant of Theorem 4.5 of RR-6968 with a coarser sampling hypothesis. Let X be a Riemannian manifold with positive strong convexity radius, f : X → ℝ tame and c-Lipschitz (c ≥ 0), 0 < δ with δ below the convexity radius, and L a finite geodesic (3δ/8)-sample of the superlevel set F^α (every point of F^α lies within 3δ/8 of L). Then there is a multi-bijection γ between the copies of D₀f and the copies of the 0-th persistence diagram of the upper-star Rips filtration R_δ(L) (vertex values f) satisfying assertions (i)–(iv) above α with radius cδ (SatisfiesIIV γ α (cδ)). The published theorem_4_5 is the same statement with a δ/4-sample.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.8), for the proof of the ORIGINAL frozen statement theorem_4_8 (8f14d99e) that avoids the unjustified external-ball comparison of the paper's netting step.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips

open Bundle
open scoped ContDiff Manifold

namespace PersistClust.Count

theorem theorem_4_5_net38
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
    (α : ℝ) (hL : IsGeodesicSample (L : Set X) (superlevel f α) ((3 * δ / 8))) :
    ∃ γ : Copies (diagram0 f) ≃
        Copies (ripsDiagram (fun x y : L => dist (x : X) (y : X)) (fun x : L => f x) δ),
      SatisfiesIIV γ α (c * δ)
    := by sorry
