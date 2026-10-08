-- Prove2me | Theorems.Thm_PersistClust_Count_lemma_4_3
-- name    : PersistClust.Count.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:39:12.161834+00:00
-- url     : https://prove2.me/theorems/95786ee7-8a9f-4566-a60c-775ecd93a34d
-- title:
--   Lemma 4.3, p. 17 — L is a geodesic ε-sample of 𝔽^α with probability ≥ 1 − 𝒩_{ε/2}(𝔽^α)e^{−n(α−cε)𝒱_{ε/2}(𝔽^α)}
-- statement:
--   Let $\mathbb X$ be an $m$-dimensional Riemannian manifold with geodesic distance $d_{\mathbb X}$ and $m$-dimensional Hausdorff measure $\mathcal H^m$, and let $f:\mathbb X\to\mathbb R$ be a probability density with respect to $\mathcal H^m$ that is $c$-Lipschitz ($c\ge0$). Let $L=\{x_1,\dots,x_n\}$ be $n$ points drawn i.i.d. according to $f$. Then for every $\varepsilon>0$ and every $\alpha>c\varepsilon$,
--   $$\Pr\big[L\text{ is not a geodesic }\varepsilon\text{-sample of }\mathbb F^\alpha\big]\;\le\;\mathcal N_{\varepsilon/2}(\mathbb F^\alpha)\,e^{-n(\alpha-c\varepsilon)\mathcal V_{\varepsilon/2}(\mathbb F^\alpha)},$$
--   where $\mathbb F^\alpha=f^{-1}([\alpha,+\infty))$, $\mathcal N_{\varepsilon/2}$ is the covering number by closed geodesic balls of radius $\varepsilon/2$ centered anywhere, and $\mathcal V_{\varepsilon/2}(\mathbb F^\alpha)=\inf_{x\in\mathbb F^\alpha}\mathcal H^m(B_{\mathbb X}(x,\varepsilon/2))$.
--
--   This is the first step of the main theorem: with high probability the sample covers the superlevel set $\mathbb F^{c\delta}$ at scale $\delta/4$.
--
--   **Formalization Note** "With probability at least $1-B$" is written as an upper bound on the (outer) measure of the failure event, which is the stronger form when the event is not measurable. The right-hand side is computed in $[0,+\infty]$, with $e^{-\infty}=0$ and $0\cdot\infty=0$. $\mathcal H^m$ is Mathlib's unnormalized Hausdorff measure of dimension $m=\dim\mathbb X$ (see the setting definitions).
-- source:
--   Chazal, Guibas, Oudot, Skraba, Persistence-Based Clustering in Riemannian Manifolds, INRIA RR-6968 (HAL inria-00389390v1, 2009), p. 17, Lemma 4.3

import Mathlib
import Definitions.Def_PersistClust_Count_Setting

open MeasureTheory Bundle
open scoped ContDiff Manifold

namespace PersistClust.Count

theorem lemma_4_3
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {X : Type*} [MetricSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
    [RiemannianBundle (fun x : X ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : X ↦ TangentSpace I x)]
    [IsRiemannianManifold I X] [MeasurableSpace X] [BorelSpace X]
    (f : X → ℝ) (c : ℝ) (hc : 0 ≤ c) (hLip : ∀ x y, |f x - f y| ≤ c * dist x y)
    (hdens : IsDensity (μH[(Module.finrank ℝ E : ℝ)] : Measure X) f)
    (ε α : ℝ) (hε : 0 < ε) (hα : c * ε < α) (n : ℕ) :
    sampleMeasure (μH[(Module.finrank ℝ E : ℝ)] : Measure X) n f
        {pts | ¬ IsGeodesicSample (Set.range pts) (superlevel f α) ε}
      ≤ (coveringNumber (ε / 2) (superlevel f α) : ENNReal)
        * expBound (n * (α - c * ε))
            (minBallMeasure (μH[(Module.finrank ℝ E : ℝ)] : Measure X) (ε / 2) (superlevel f α)) := by sorry

end PersistClust.Count
