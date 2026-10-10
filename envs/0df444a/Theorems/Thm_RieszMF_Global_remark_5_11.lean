-- Prove2me | Theorems.Thm_RieszMF_Global_remark_5_11
-- name    : RieszMF.Global.remark_5_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:11:50.583811+00:00
-- url     : https://prove2.me/theorems/f6e1909b-c8a5-423a-b72d-74d4fcef2d00
-- title:
--   Remark 5.11, (5.33), p. 26 — smeared-energy bound when only $\hat{\mathsf g}\ge0$
-- statement:
--   Let $d\ge3$, $0\le s\le d-2$, and let $h:\mathbb R^d\to\mathbb R$ be a potential of order $s$ satisfying (i), (iii) with $r_0=\infty$, (iv), and $\hat h\ge0$ on $\mathbb R^d\setminus\{0\}$ (in place of (vi)). There is $C>0$ and, for every $d/(s+2)<p\le\infty$, a constant $C_p>0$ such that for every pairwise distinct $x_N$, every probability density $\mu\in L^\infty$ (with a logarithmic moment if $s=0$) and every choice of $0<\eta_1,\dots,\eta_N<2^{-\frac{dp-d+2p}{d(p-1)}}\|\mu\|_{L^\infty}^{-1/d}$,
--
--   $$\frac1{N^2}\sum_{1\le i\ne j\le N}\big(h(x_j-x_i)-h_{\eta_i}(x_j-x_i)\big)_+\le F_N(x_N,\mu)+\sum_{i=1}^N\frac{C\eta_i^{-s}(1+|\log\eta_i|\mathbf 1_{s=0})}{N^2}+\frac{C_p\|\mu\|_{L^\infty}^{\gamma}}{N}\sum_{i=1}^N\eta_i^{\lambda}\big(1+(|\log\eta_i|+|\log\|\mu\|_{L^\infty}|)\mathbf 1_{s=0}\big),$$
--
--   where $h_\eta=h*\delta^{(\eta)}_0$, $F_N$ is the modulated energy of $h$, and $\gamma=\gamma_{s,p}$, $\lambda=\lambda_{s,p}$ are the exponents (5.21).
--
--   The bound controls the short-distance part of the interaction by the modulated energy; Corollary 5.14 applies it to $h=-\Delta\mathsf g$ with $s+2$ in place of $s$.
--
--   **Formalization Note** The remark is stated for a generic potential $h$ of order $s$, because Corollary 5.14 uses it for $-\Delta\mathsf g$ of order $s+2$. The constant $C$ does not depend on $p$, $C_p$ does. For $p=\infty$ the exponents are the limits $\gamma=(2+s)/(d+2)$, $\lambda=2(d-s)/(d+2)$, and the range exponent is $(d+2)/d$.
-- source:
--   Rosenzweig & Serfaty, Global-in-time mean-field convergence for singular Riesz-type diffusive flows, arXiv:2108.09878v1, p. 26, Remark 5.11, (5.33); setting of Proposition 5.8, pp. 24–25

import Mathlib
import Definitions.Def_RieszMF_Global_Setting

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace RieszMF.Global

/-- Remark 5.11 (p. 26), (5.33), for a generic potential `h` of order `s ∈ [0, d - 2]` with (i),
(iii) for `r₀ = ∞`, (iv), and `ĥ ≥ 0` away from the origin (in place of (vi)): there are `C > 0`
and, for every `d/(s+2) < p ≤ ∞`, `C_p > 0` such that for every pairwise distinct `x_N`, every
`μ ∈ 𝒫 ∩ L^∞` (with a log moment if `s = 0`) and every
`0 < η_i < 2^{-(dp-d+2p)/(d(p-1))} ‖μ‖_{L^∞}^{-1/d}`,
`(1/N²) ∑_{i≠j} (h(x_j - x_i) - h_{η_i}(x_j - x_i))_+ ≤ F_N(x_N, μ)
  + ∑_i C η_i^{-s}(1 + |log η_i| 1_{s=0})/N²
  + (C_p ‖μ‖_{L^∞}^γ / N) ∑_i η_i^λ (1 + (|log η_i| + |log ‖μ‖_{L^∞}|) 1_{s=0})`,
`γ = γ_{s,p}`, `λ = λ_{s,p}`. -/
theorem remark_5_11 :
    ∀ (d : ℕ) (s : ℝ), 3 ≤ d → 0 ≤ s → s ≤ (d : ℝ) - 2 →
    ∀ h : RieszMF.Linear.E d → ℝ, RieszMF.Linear.AssumpI h → GloballySuperharmonic h → RieszMF.Linear.AssumpIV d s h →
      (∃ hhat : RieszMF.Linear.E d → ℝ, (∀ ξ : RieszMF.Linear.E d, ξ ≠ 0 → 0 ≤ hhat ξ) ∧ RieszMF.Linear.FTOffZero h hhat) →
    ∃ C : ℝ, 0 < C ∧
    ∀ p : ℝ≥0∞, ENNReal.ofReal ((d : ℝ) / (s + 2)) < p →
    ∃ Cp : ℝ, 0 < Cp ∧
    ∀ N : ℕ, 0 < N →
    ∀ x : Fin N → RieszMF.Linear.E d, Pairwise (fun i j => x i ≠ x j) →
    ∀ μ : RieszMF.Linear.E d → ℝ, IsProbDensity μ → (s = 0 → RieszMF.Linear.LogMoment μ) →
    ∀ η : Fin N → ℝ, (∀ i, 0 < η i ∧ η i < etaMax d p (supNorm μ)) →
      smearGap N h x η ≤
        RieszMF.Linear.modEnergy N h x μ +
          ∑ i, C * η i ^ (-s) * (1 + |Real.log (η i)| * (if s = 0 then 1 else 0)) / (N : ℝ) ^ 2 +
          Cp * supNorm μ ^ gam d s p / N *
            ∑ i, η i ^ lam d s p *
              (1 + (|Real.log (η i)| + |Real.log (supNorm μ)|) * (if s = 0 then 1 else 0)) := by sorry

end RieszMF.Global
