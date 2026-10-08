-- Prove2me | Theorems.Thm_PersistClust_Count_theorem_4_8
-- name    : PersistClust.Count.theorem_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:40:39.920178+00:00
-- url     : https://prove2.me/theorems/8f14d99e-9520-4f95-a91a-167ff27ea090
-- title:
--   Theorem 4.8, p. 22 — with probability ≥ 1 − 𝒩_{δ/8}(𝔽^{cδ})e^{−n¾cδ𝒱_{δ/8}(𝔽^{cδ})} the algorithm outputs as many clusters as f has peaks of prominence ≥ d₂
-- statement:
--   Let $\mathbb X$ be an $m$-dimensional Riemannian manifold, possibly with boundary, with geodesic distance $d_{\mathbb X}$, $m$-dimensional Hausdorff measure $\mathcal H^m$ and positive strong convexity radius $\varrho_c(\mathbb X)$. Let $f:\mathbb X\to\mathbb R$ be a tame $c$-Lipschitz probability density with respect to $\mathcal H^m$, $c>0$. Assume the $0$-th persistence diagram $D_0f$ of the superlevel-set filtration of $f$ is $(d_1,d_2)$-separated, with $d_2>d_1\ge0$. Let $\delta$ be a parameter with
--   $$0<\delta<\min\Big\{\varrho_c(\mathbb X),\ \frac{d_2-d_1}{5c}\Big\},$$
--   and $\tau$ a threshold in $(d_1+2c\delta,\ d_2-3c\delta)$. Draw $n$ points $x_1,\dots,x_n$ i.i.d. according to $f$ and run the clustering algorithm on the values $f(x_i)$, the distances $d_{\mathbb X}(x_i,x_j)$ and the parameters $\delta,\tau$. Then the probability that, for some sorting order of line 1, the number of clusters output differs from the number of peaks of $f$ of prominence at least $d_2$ is at most
--   $$\mathcal N_{\delta/8}(\mathbb F^{c\delta})\,e^{-n\frac34c\delta\,\mathcal V_{\delta/8}(\mathbb F^{c\delta})}.$$
--   Equivalently, with probability at least $1-\mathcal N_{\delta/8}(\mathbb F^{c\delta})e^{-n\frac34c\delta\mathcal V_{\delta/8}(\mathbb F^{c\delta})}$ the algorithm returns as many clusters as $f$ has $d_2$-prominent peaks, whatever the tie-breaking. Here $\mathbb F^{c\delta}=f^{-1}([c\delta,+\infty))$, and the number of peaks of prominence at least $d_2$ is the total multiplicity of $D_0f$ in $\Delta^S_{d_2}=\{p_y\le p_x-d_2\}$.
--
--   This is the main result of the paper: a guarantee on the number of clusters recovered by persistence-based clustering from i.i.d. samples on a possibly non-compact manifold.
--
--   **Formalization Note** $c>0$ is required because the paper divides by $c$. The probability statement bounds the outer measure of the failure event, with the right-hand side in $[0,+\infty]$ ($e^{-\infty}=0$, $0\cdot\infty=0$). The algorithm is the union-find procedure of §3, run on the index set $\{1,\dots,n\}$; the statement quantifies over every sorting permutation. $\mathcal H^m$ is Mathlib's unnormalized Hausdorff measure, a constant multiple of the normalized one; the theorem is invariant under that rescaling.
-- source:
--   Chazal, Guibas, Oudot, Skraba, Persistence-Based Clustering in Riemannian Manifolds, INRIA RR-6968 (HAL inria-00389390v1, 2009), p. 22, Theorem 4.8

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips
import Definitions.Def_PersistClust_Count_Algorithm

open MeasureTheory Bundle
open scoped ContDiff Manifold

namespace PersistClust.Count

theorem theorem_4_8
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
    (τ : ℝ) (hτ₁ : d₁ + 2 * c * δ < τ) (hτ₂ : τ < d₂ - 3 * c * δ) (n : ℕ) :
    sampleMeasure (μH[(Module.finrank ℝ E : ℝ)] : Measure X) n f
        {pts | ¬ ∀ σ : Fin n ≃ Fin n, IsSortOrder (f ∘ pts) σ →
          (numClusters (f ∘ pts) (fun i j => dist (pts i) (pts j)) δ τ σ : ℕ∞)
            = prominentCount (diagram0 f) d₂}
      ≤ (coveringNumber (δ / 8) (superlevel f (c * δ)) : ENNReal)
        * expBound (n * (3 / 4 * c * δ))
            (minBallMeasure (μH[(Module.finrank ℝ E : ℝ)] : Measure X) (δ / 8)
              (superlevel f (c * δ))) := by sorry

end PersistClust.Count
