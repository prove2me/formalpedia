-- Prove2me | Theorems.Thm_RieszMF_Global_remark_5_13
-- name    : RieszMF.Global.remark_5_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:11:51.929794+00:00
-- url     : https://prove2.me/theorems/dcea050d-4a37-45cc-b5d1-9e0e84481aa3
-- title:
--   Remark 5.13, (5.43), p. 28 — $F_N\ge-C\|\mu\|_{L^\infty}^{s/d}N^{-(d-s)/d}$ for $d-2<s<d$
-- statement:
--   In the setting of Proposition 5.12 ($d\ge3$, $d-2<s<d$, $h$ with (i), global (iii), (iv) of order $s$, and an extension $\mathsf G$ with (1.14)–(1.17) on all of $\mathbb R^{d+m}$), there is $C>0$ such that for every pairwise distinct $x_N$ and every probability density $\mu\in L^\infty$,
--
--   $$F_N(x_N,\mu)\ge-C\,\|\mu\|_{L^\infty}^{s/d}\,N^{-\frac{d-s}d}.$$
--
--   The remark obtains this from (5.34) with $\eta_i=(\|\mu\|_{L^\infty}N)^{-1/d}$; it is the lower bound used for $-\Delta\mathsf g$ in Corollary 5.14.
-- source:
--   Rosenzweig & Serfaty, Global-in-time mean-field convergence for singular Riesz-type diffusive flows, arXiv:2108.09878v1, p. 28, Remark 5.13, (5.43)

import Mathlib
import Definitions.Def_RieszMF_Global_Setting

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace RieszMF.Global

/-- Remark 5.13 (p. 28), (5.43), in the setting of Proposition 5.12: there is `C > 0` such that
`F_N(x_N, μ) ≥ -C ‖μ‖_{L^∞}^{s/d} N^{-(d-s)/d}` for every pairwise distinct `x_N` and every
`μ ∈ 𝒫 ∩ L^∞`. -/
theorem remark_5_13 :
    ∀ (d : ℕ) (s : ℝ), 3 ≤ d → (d : ℝ) - 2 < s → s < (d : ℝ) →
    ∀ h : RieszMF.Linear.E d → ℝ, RieszMF.Linear.AssumpI h → GloballySuperharmonic h → RieszMF.Linear.AssumpIV d s h →
    ∀ (m : ℕ), 0 < m → ∀ G : RieszMF.Linear.E (d + m) → ℝ, IsGlobalExtension d m h s G →
    ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, 0 < N →
    ∀ x : Fin N → RieszMF.Linear.E d, Pairwise (fun i j => x i ≠ x j) →
    ∀ μ : RieszMF.Linear.E d → ℝ, IsProbDensity μ →
      -C * supNorm μ ^ (s / d) * (N : ℝ) ^ (-(((d : ℝ) - s) / d)) ≤ RieszMF.Linear.modEnergy N h x μ := by sorry

end RieszMF.Global
