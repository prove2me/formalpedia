-- Prove2me | Theorems.Thm_PolymerEndpoint_GeoLoc_theorem_5_3
-- name    : PolymerEndpoint.GeoLoc.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:33:27.239984+00:00
-- url     : https://prove2.me/theorems/0c47db3c-06e0-4b8e-b4b8-238f044a1e0e
-- title:
--   Theorem 5.3, p. 39 — Cesàro average of max_x f_i(x): → 0 a.s. if β ≤ β_c, liminf ≥ c > 0 a.s. if β > β_c
-- statement:
--   Let $d\ge1$, let $\mathfrak L$ be a non-degenerate law with $\lambda(\alpha)<\infty$ for $\alpha\in[-2\beta,2\beta]$ (1.1), $\beta\ge0$, and let $f_i=\rho_i(\omega_i=\cdot)$ be the endpoint distributions of the directed polymer in an environment with law $\mathfrak L$.
--
--   1. If $0\le\beta\le\beta_c$, then
--   $$\lim_{n\to\infty}\frac1n\sum_{i=0}^{n-1}\max_{x\in\mathbb Z^d}f_i(x)=0\quad\text{a.s.}$$
--   2. If $\beta>\beta_c$, then there exists $c>0$ such that
--   $$\liminf_{n\to\infty}\frac1n\sum_{i=0}^{n-1}\max_{x\in\mathbb Z^d}f_i(x)\ge c\quad\text{a.s.}\qquad(5.1)$$
--
--   This is the paper's proof of Theorem D of Comets, Shiga and Yoshida: the endpoint is atomically localized, in the Cesàro sense, exactly in the low-temperature phase. Part 1 is the estimate (7.6) used for the high-temperature half of the goal theorem.
--
--   **Formalization Note.** $\beta>\beta_c$ and $0\le\beta\le\beta_c$ are encoded through Theorem A as $\lim\mathbf E(F_n)<\lambda(\beta)$ and $\lim\mathbf E(F_n)=\lambda(\beta)$. Non-degeneracy of $\mathfrak L$ is the standing assumption of §1.1. The constant $c$ is quantified for the given probability space, as printed.
-- source:
--   Bates and Chatterjee, The endpoint distribution of directed polymers, arXiv:1612.03443v5, p. 39, Theorem 5.3 (restating Theorem D, p. 9)

import Mathlib
import Definitions.Def_PolymerEndpoint_GeoLoc_Functionals
open MeasureTheory ProbabilityTheory Filter Topology

namespace PolymerEndpoint.GeoLoc

/-- Theorem 5.3: the Cesàro average of `max_x f_i(x)` tends to `0` a.s. at high temperature and
has `liminf ≥ c > 0` a.s. at low temperature. -/
theorem theorem_5_3 (d : ℕ) (hd : 1 ≤ d) (𝔏 : Measure ℝ) [IsProbabilityMeasure 𝔏]
    (h𝔏 : ∀ c : ℝ, 𝔏 ≠ Measure.dirac c) (β : ℝ) (hβ : 0 ≤ β)
    (hmgf : ∀ α ∈ Set.Icc (-2 * β) (2 * β), Integrable (fun x => Real.exp (α * x)) 𝔏)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : PolymerEndpoint.Atomic.Cell d → Ω → ℝ) (hX : PolymerEndpoint.Atomic.IsEnvironment X 𝔏 P) :
    (HighTemp d 𝔏 β → ∀ᵐ a ∂P, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
        ∑ i ∈ Finset.range n, ⨆ x, PolymerEndpoint.Atomic.endpt X β i a x) atTop (𝓝 0)) ∧
    (LowTemp d 𝔏 β → ∃ c : ℝ, 0 < c ∧ ∀ᵐ a ∂P, c ≤ liminf (fun n : ℕ => (n : ℝ)⁻¹ *
        ∑ i ∈ Finset.range n, ⨆ x, PolymerEndpoint.Atomic.endpt X β i a x) atTop) := by sorry

end PolymerEndpoint.GeoLoc
