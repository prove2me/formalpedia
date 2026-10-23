-- Prove2me | Theorems.Thm_RepRegion_Density_theorem_6_5
-- name    : RepRegion.Density.theorem_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:14.298929+00:00
-- url     : https://prove2.me/theorems/d087f981-a981-4fd0-b128-31965d8a4fff
-- title:
--   Theorem 6.5, p. 28 — for an arbitrarily precise family of RRS methods, lim_m limsup_n ∫|g_X − ĝ_{n,m}| dμ = 0 almost surely
-- statement:
--   Let $(M, d)$ be a metric space whose closed balls are measurable, let $X_1, X_2, \dots$ be i.i.d. $M$-valued random variables with law $P_X$, and let $\mu$ be a measure on $M$ such that $P_X$ has a density $g_X \ge 0$ with respect to $\mu$, continuous on $M$. Let $K$ be the support of $P_X$; suppose $K$ is compact, $P_X(K) = 1$, and for some $\delta > 0$ the closed $\delta$-neighbourhood of $K$ has finite measure,
--   $$\mu\bigl(\{x \in M : d(x, y) \le \delta \text{ for some } y \in K\}\bigr) < \infty.$$
--   Let $\{(\mathcal C, f_m) : m \in \mathbb N\}$ be an arbitrarily precise family of RRS methods, where $(\mathcal C, \Theta, R)$ is a uniform-scale class that is uniformly continuous with respect to $P_X$. Suppose each $(\mathcal C, f_m)$ is sample-covering, sample-intersecting, has asymptotically-bounded cardinality and is uniformly positive with respect to $\mu$, and write $\hat g_{n,m} = \hat g_n(\cdot\,; f_m)$. Then almost surely
--   $$\lim_{m \to \infty} \Bigl( \limsup_{n \to \infty} \int_M \bigl|g_X - \hat g_{n,m}\bigr| \, d\mu \Bigr) = 0.$$
--
--   This is the main density-estimation result of the paper: the region-average estimate built from any arbitrarily precise family of RRS methods with these properties is consistent in integrated absolute error. Histograms, density estimation trees and the paper's minimum-dominating-set and $k$-center methods are instances.
--
--   **Formalization Note.** The page prints the limit as "$= \varepsilon$" with $\varepsilon$ unbound; the proof ends with "$\limsup_n \int_M |g_X - \hat g_{n,m}|\,d\mu < \varepsilon$" for arbitrary $\varepsilon > 0$, and the paper's applications (Corollaries 7.1, 7.2) conclude "$= 0$", so the statement says $0$. The page assumes $g_X$ continuous on $K$; the statement assumes it continuous on all of $M$, the hypothesis of Theorem 6.4 that the proof invokes (this excludes densities that jump at the boundary of $K$). The regions output by the methods are assumed to have finite $\mu$-measure, so that $\hat g$ is defined. The integral is a lower Lebesgue integral in $[0, \infty]$ and the limit superior is taken in $[0, \infty]$, so an infinite error is allowed for small $m$. Uniform continuity of the class uses the small-scale convention described in Theorem 6.1. The reference measure $\mu$ is arbitrary.
-- source:
--   Estes, Ball & Lovell, Data Exploration by Representative Region Selection: Axioms and Convergence, SSRN preprint 3005997, p. 28, Theorem 6.5

import Mathlib
import Definitions.Def_RepRegion_Density_Model

open MeasureTheory ProbabilityTheory Filter Topology ENNReal

namespace RepRegion.Density

theorem theorem_6_5 {M Ω Θ : Type*}
    [MetricSpace M] [MeasurableSpace M] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → M)
    (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hball : ∀ (x : M) (r : ℝ), MeasurableSet (Metric.closedBall x r))
    (μ : Measure M) (g : M → ℝ) (hgm : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (hdens : P.map (X 0) = μ.withDensity (fun x => ENNReal.ofReal (g x)))
    (hgc : Continuous g)
    (K : Set M) (hK : K = supp (P.map (X 0))) (hKc : IsCompact K)
    (hK1 : P.map (X 0) K = 1)
    (hnbhd : ∃ δ : ℝ, 0 < δ ∧ μ {x | ∃ y ∈ K, dist x y ≤ δ} ≠ ⊤)
    (C : Set (Set M)) (R : Θ → ℝ → Set M)
    (hUS : UniformScale C R) (hUC : UnifContWrt C R (P.map (X 0)))
    (f : ℕ → Finset M → Finset (Set M)) (hf : ∀ m, IsRRSMethod C (f m))
    (hAP : ArbitrarilyPrecise P X f)
    (hcov : ∀ m, SampleCovering (f m)) (hint : ∀ m, SampleIntersecting (f m))
    (hcard : ∀ m, AsympBoundedCard P X (f m))
    (hpos : ∀ m, UniformlyPositive C (f m) μ)
    (hfin : ∀ (m : ℕ) (S : Finset M), ∀ A ∈ f m S, μ A ≠ ⊤) :
    ∀ᵐ ω ∂P, Tendsto (fun m : ℕ => limsup (fun n : ℕ =>
        ∫⁻ x, ENNReal.ofReal |g x - ghat μ (f m) X n ω x| ∂μ) atTop) atTop (𝓝 0) := by sorry

end RepRegion.Density
