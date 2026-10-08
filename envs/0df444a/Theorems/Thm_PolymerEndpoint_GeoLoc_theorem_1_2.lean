-- Prove2me | Theorems.Thm_PolymerEndpoint_GeoLoc_theorem_1_2
-- name    : PolymerEndpoint.GeoLoc.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:34:47.319502+00:00
-- url     : https://prove2.me/theorems/4d919790-364b-49a6-af25-068bf59e548b
-- title:
--   Theorem 1.2, p. 17 (= Theorem 7.3(a),(c)) — geometric localization with positive density iff β > β_c
-- statement:
--   Let $d\ge1$, let $\mathfrak L$ be a probability law on $\mathbb R$ that is not supported on a single point, let $\beta\ge0$ satisfy (1.1): $\lambda(\alpha)=\log\mathbf E e^{\alpha X}<\infty$ for $\alpha\in[-2\beta,2\beta]$, and let $f_i=\rho_i(\omega_i=\cdot)$ be the endpoint distributions of the $(d+1)$-dimensional directed polymer in an environment with law $\mathfrak L$. For $\delta,K$ let $\mathcal G_{\delta,K}$ be the set of probability mass functions on $\mathbb Z^d$ giving mass $>1-\delta$ to some set of $\ell^1$-diameter at most $K$ (7.1).
--
--   1. If $\beta>\beta_c$, there is **geometric localization with positive density**: for every $\delta>0$ there are $K<\infty$ and $\theta>0$ such that
--   $$\liminf_{n\to\infty}\frac1n\sum_{i=0}^{n-1}\mathbb 1_{\{f_i\in\mathcal G_{\delta,K}\}}\ge\theta\quad\text{a.s.}$$
--   Moreover $K$ and $\theta$ are deterministic: they depend only on $\delta$, $\mathfrak L$, $\beta$ and $d$, and the bound holds for every environment with law $\mathfrak L$.
--   2. If $0\le\beta\le\beta_c$, then for any $K$ and any $\delta\in(0,1)$,
--   $$\lim_{n\to\infty}\frac1n\sum_{i=0}^{n-1}\mathbb 1_{\{f_i\in\mathcal G_{\delta,K}\}}=0\quad\text{a.s.}$$
--
--   So positive-density geometric localization of the endpoint, a property of its spatial shape and not only of its atoms, characterises the low-temperature phase in every dimension and for every disorder law with the exponential moments (1.1).
--
--   **Formalization Note.** $\beta>\beta_c$ and $0\le\beta\le\beta_c$ are encoded through Theorem A as $\lim\mathbf E(F_n)<\lambda(\beta)$ and $\lim\mathbf E(F_n)=\lambda(\beta)$. Determinism of $K,\theta$ is expressed by choosing them before quantifying over all probability spaces (in the lowest universe) and environments with law $\mathfrak L$. Part 1 is stated for every $\delta>0$ as in §7 (for $\delta\ge1$ it is trivial); part 2 is stated for $\delta\in(0,1)$ as printed, since it fails for $\delta\ge1$. Non-degeneracy of $\mathfrak L$ is the standing assumption of §1.1.
-- source:
--   Bates and Chatterjee, The endpoint distribution of directed polymers, arXiv:1612.03443v5, p. 17, Theorem 1.2; p. 49, Theorem 7.3(a),(c); p. 46, (7.1); p. 16, §1.5

import Mathlib
import Definitions.Def_PolymerEndpoint_GeoLoc_Functionals
open MeasureTheory ProbabilityTheory Filter Topology

namespace PolymerEndpoint.GeoLoc

open Classical in
/-- Theorem 1.2 (= Theorem 7.3(a),(c)): geometric localization with positive density holds,
with deterministic `K`, `θ`, in the low-temperature phase, and fails for every `K` and every
`δ ∈ (0, 1)` in the high-temperature phase. -/
theorem theorem_1_2 (d : ℕ) (hd : 1 ≤ d) (𝔏 : Measure ℝ) [IsProbabilityMeasure 𝔏]
    (h𝔏 : ∀ c : ℝ, 𝔏 ≠ Measure.dirac c) (β : ℝ) (hβ : 0 ≤ β)
    (hmgf : ∀ α ∈ Set.Icc (-2 * β) (2 * β), Integrable (fun x => Real.exp (α * x)) 𝔏) :
    (LowTemp d 𝔏 β → ∀ δ : ℝ, 0 < δ → ∃ K : ℝ, ∃ θ : ℝ, 0 < θ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : PolymerEndpoint.Atomic.Cell d → Ω → ℝ), PolymerEndpoint.Atomic.IsEnvironment X 𝔏 P → ∀ᵐ a ∂P,
          θ ≤ liminf (fun n : ℕ => (n : ℝ)⁻¹ *
            ∑ i ∈ Finset.range n, if InG δ K (PolymerEndpoint.Atomic.endpt X β i a) then (1 : ℝ) else 0) atTop) ∧
    (HighTemp d 𝔏 β → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : PolymerEndpoint.Atomic.Cell d → Ω → ℝ), PolymerEndpoint.Atomic.IsEnvironment X 𝔏 P → ∀ K : ℝ, ∀ δ ∈ Set.Ioo (0 : ℝ) 1,
          ∀ᵐ a ∂P, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
            ∑ i ∈ Finset.range n, if InG δ K (PolymerEndpoint.Atomic.endpt X β i a) then (1 : ℝ) else 0) atTop (𝓝 0)) := by sorry

end PolymerEndpoint.GeoLoc
