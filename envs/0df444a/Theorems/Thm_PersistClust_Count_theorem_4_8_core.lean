-- Prove2me | Theorems.Thm_PersistClust_Count_theorem_4_8_core
-- name    : PersistClust.Count.theorem_4_8_core
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T10:24:28.725456+00:00
-- url     : https://prove2.me/theorems/027bdb99-2f03-4b8a-941a-634dd56235cb
-- title:
--   Theorem 4.8 deterministic core: with the Theorem-4.5 multi-bijection, netting, sample positivity and tau-genericity, Procedure 1's output count equals the d2-prominent peak count for every sort order
-- statement:
--   This is the conditional correctness core of Theorem 4.8 of RR-6968 (p. 22).
--
--   Let $\mathbb{X}$ be a Riemannian manifold with positive strong convexity radius and let $f : \mathbb{X} \to \mathbb{R}$ be a tame $c$-Lipschitz density ($c > 0$, $\int f\,d\mu = 1$), with $D_0 f$ being $(d_1, d_2)$-separated for $d_1 < d_2$. Fix $\delta > 0$ with $\delta < \varrho_c(\mathbb{X})$ and $\delta < (d_2 - d_1)/(5c)$, and a prominence threshold $\tau$ with $d_1 + 2c\delta < \tau < d_2 - 3c\delta$, and put $\alpha := c\delta$.
--
--   Let $x_1, \dots, x_n$ be a sample such that (i) the distinct points $L$ form a geodesic $\delta/4$-sample of the superlevel set $\mathbb{F}^{c\delta}$, (ii) all sample values are strictly positive, and (iii) the upper-star Rips diagram of the sample at scale $\delta$ has no bar born exactly at the threshold $\tau$ with death at or below $0$ — the generic-position replacement for the almost-sure $\tau$-avoidance event of the probabilistic proof. Suppose moreover that there is a multi-bijection $\gamma$ between the copies of $D_0 f$ and those of the Rips diagram of $(L, f|_L)$ at scale $\delta$ satisfying assertions (i)–(iv) of Theorem 4.5 with threshold $\alpha = c\delta$ and radius $r = c\delta$.
--
--   Then, for every sort order $\sigma$ of the samples, the number of clusters output by Procedure 1 at prominence threshold $\tau$ equals the number of $d_2$-prominent peaks of $D_0 f$. In other words: given the Theorem-4.5 closeness of the two diagrams, the algorithm is correct on the netted, positive, $\tau$-generic event, independently of tie-breaking.
--
--   This is the deterministic core that the root theorem's probabilistic argument reduces to: the root discharges the netting failure probability and the two null events by the sampling bound, and consumes the present statement with the multi-bijection supplied by Theorem 4.5.
-- source:
--   Chazal, Guibas, Oudot, Skraba, Persistence-Based Clustering in Riemannian Manifolds, INRIA RR-6968 (HAL inria-00389390v1, 2009), p. 22, the deterministic core of the proof of Theorem 4.8 (the multi-bijection enters as a hypothesis)

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips
import Definitions.Def_PersistClust_Count_Algorithm

open MeasureTheory Bundle
open scoped ContDiff Manifold

namespace PersistClust.Count

/-- **Conditional correctness core of Theorem 4.8.** On a netted sample with positive sample
values, τ-generic Rips-critical structure, and a Theorem-4.5 multi-bijection, Procedure 1's
cluster count is exactly the number of `d₂`-prominent peaks of `D₀f`, for EVERY sort order.
This is the deterministic core the root's probabilistic argument reduces to (failure ⟹
¬netted, up to the a.s. positivity and τ-avoidance null sets). -/
theorem theorem_4_8_core
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
    -- (1) netting: L is a geodesic δ/4-sample of F^{cδ}
    (hnet : IsGeodesicSample (L : Set X) (superlevel f (c * δ)) (δ / 4))
    -- (2) positivity: deterministic replacement for the a.s. {f = 0} null-set excision
    (hpos : ∀ i : Fin n, 0 < f (pts i))
    -- (2b) τ-genericity: no Rips bar of the sample is born exactly at the threshold τ
    -- with death at or below 0 (deterministic replacement for the a.s. τ-avoidance event;
    -- without it the algorithm-count region (birth ≥ τ, closed) and the prominence-count
    -- region (birth > τ, open) differ at the (τ, d ≤ 0) edge — e.g. the sample's essential
    -- bar (max g, ⊥) when max g = τ exactly).
    (hτexc : ∀ d : EReal, d ≤ ((0 : ℝ) : EReal) →
      ripsDiagram (fun i j => dist (pts i) (pts j)) (f ∘ pts) δ (((τ : ℝ) : EReal), d) = 0)
    -- (3) the Theorem-4.5 multi-bijection at α = cδ, radius cδ — literally 4_5's γ over L
    (γ : Copies (diagram0 f) ≃
        Copies (ripsDiagram (fun x y : L => dist (x : X) (y : X)) (fun x : L => f x) δ))
    (hγ : SatisfiesIIV γ (c * δ) (c * δ)) :
    ∀ σ : Fin n ≃ Fin n, IsSortOrder (f ∘ pts) σ →
      (numClusters (f ∘ pts) (fun i j => dist (pts i) (pts j)) δ τ σ : ℕ∞)
        = prominentCount (diagram0 f) d₂ := by
  sorry

end PersistClust.Count
