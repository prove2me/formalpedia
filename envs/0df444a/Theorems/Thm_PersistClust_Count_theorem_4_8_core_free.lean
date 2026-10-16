-- Prove2me | Theorems.Thm_PersistClust_Count_theorem_4_8_core_free
-- name    : PersistClust.Count.theorem_4_8_core_free
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-16T05:30:24.850703+00:00
-- url     : https://prove2.me/theorems/23c0d6cb-138a-4038-ac49-d53d6027f3dd
-- title:
--   Theorem 4.8 deterministic core without netting, positivity or τ-genericity: the multi-bijection alone forces the right cluster count
-- statement:
--   Strengthening of the accepted theorem_4_8_core (027bdb99): its netting hypothesis, its positivity hypothesis (all sample values > 0) and its τ-genericity hypothesis (no Rips bar born exactly at τ with death ≤ 0) are dropped. Under the hypotheses of Theorem 4.8 of RR-6968 (tame c-Lipschitz density f, (d₁, d₂)-separated D₀f, 0 < δ < (d₂ − d₁)/(5c), τ ∈ (d₁ + 2cδ, d₂ − 3cδ)), for a sample pts : Fin n → X whose distinct points form the finite set L, and any multi-bijection γ between the copies of D₀f and of the Rips diagram of L at δ satisfying assertions (i)–(iv) at threshold and radius cδ, Procedure 1 returns exactly prominentCount (D₀f) d₂ clusters for every sort order.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.8), for the proof of the ORIGINAL frozen statement theorem_4_8 (8f14d99e) that avoids the unjustified external-ball comparison of the paper's netting step.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips
import Definitions.Def_PersistClust_Count_Algorithm

open MeasureTheory Bundle
open scoped ContDiff Manifold

namespace PersistClust.Count

theorem theorem_4_8_core_free
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {X : Type*} [MetricSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
    [RiemannianBundle (fun x : X ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : X ↦ TangentSpace I x)]
    [IsRiemannianManifold I X] [MeasurableSpace X] [BorelSpace X]
    (hconv : 0 < convexityRadius X)
    (f : X → ℝ) (c : ℝ) (hc : 0 < c) (hLip : ∀ x y, |f x - f y| ≤ c * dist x y)
    (hdens : IsDensity (μH[(Module.finrank ℝ E : ℝ)] : Measure X) f) (htame : IsTame0 f)
    (d₁ d₂ : ℝ) (hd₁ : 0 ≤ d₁) (hd : d₁ < d₂) (hsep : IsSeparated (diagram0 f) d₁ d₂)
    (δ : ℝ) (hδ : 0 < δ) (hδρ : ENNReal.ofReal δ < convexityRadius X)
    (hδc : δ < (d₂ - d₁) / (5 * c))
    (τ : ℝ) (hτ₁ : d₁ + 2 * c * δ < τ) (hτ₂ : τ < d₂ - 3 * c * δ)
    (n : ℕ) (pts : Fin n → X) (L : Finset X)
    -- (0) the sample realizes exactly the distinct points of L
    (hmem : ∀ i : Fin n, pts i ∈ L)
    (hsurj : ∀ x ∈ L, ∃ i : Fin n, pts i = x)
    -- (3) the Theorem-4.5 multi-bijection at α = cδ, radius cδ — literally 4_5's γ over L
    (γ : Copies (diagram0 f) ≃
        Copies (ripsDiagram (fun x y : L => dist (x : X) (y : X)) (fun x : L => f x) δ))
    (hγ : SatisfiesIIV γ (c * δ) (c * δ)) :
    ∀ σ : Fin n ≃ Fin n, IsSortOrder (f ∘ pts) σ →
      (numClusters (f ∘ pts) (fun i j => dist (pts i) (pts j)) δ τ σ : ℕ∞)
        = prominentCount (diagram0 f) d₂
    := by sorry
