-- Prove2me | Theorems.Thm_SAARate_Sharp_display_2_10
-- name    : SAARate.Sharp.display_2_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:05:47.312734+00:00
-- url     : https://prove2.me/theorems/29cdf5cd-48cb-48a3-bae7-d3ac973be729
-- title:
--   (2.10), p. 5 — f̂′_N(x, d) = N⁻¹ Σ_{j=1}^N h′_{ωʲ}(x, d)
-- statement:
--   Let $h:\mathbb R^m\times\Omega\to\mathbb R$ with $h(\cdot,\omega)$ convex for every $\omega$. For a sample $\omega^1,\dots,\omega^N$ with $N\ge1$, let $\hat f_N(x)=N^{-1}\sum_{j=1}^N h(x,\omega^j)$. Then for all $x,d\in\mathbb R^m$,
--   $$
--   \hat f'_N(x,d)=N^{-1}\sum_{j=1}^N h'_{\omega^j}(x,d), \tag{2.10}
--   $$
--   where $\hat f'_N(x,d)$ and $h'_{\omega^j}(x,d)$ are the directional derivatives of $\hat f_N$ and of $h(\cdot,\omega^j)$ at $x$ in direction $d$.
--
--   This identity writes $\hat f'_N(x,d)$ as a sample mean of i.i.d. variables, to which the strong law of large numbers applies in the proof of (2.6).
--
--   **Formalization Note.** The statement holds for every sample path, not only almost surely. The paper's $\omega^j$ is the Lean `s (j-1)`.
-- source:
--   Shapiro & Homem-de-Mello, On Rate of Convergence of Optimal Solutions of Monte Carlo Approximations of Stochastic Programs, preprint (SPEPS copy, edoc.hu-berlin.de), p. 5, proof of Proposition 2.2, (2.10)

import Mathlib
import Definitions.Def_SAARate_Sharp_Setting

namespace SAARate.Sharp

open MeasureTheory ProbabilityTheory Filter Topology

theorem display_2_10 {m : ℕ} {Ω : Type*} (h : E m → Ω → ℝ)
    (hconv : ∀ ω, ConvexOn ℝ Set.univ (fun x => h x ω))
    (s : ℕ → Ω) (N : ℕ) (hN : 1 ≤ N) (x d : E m) :
    dirDeriv (saaObj h s N) x d =
      (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, dirDeriv (fun y => h y (s j)) x d := by sorry

end SAARate.Sharp
