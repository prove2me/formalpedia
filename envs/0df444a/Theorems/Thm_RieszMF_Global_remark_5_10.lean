-- Prove2me | Theorems.Thm_RieszMF_Global_remark_5_10
-- name    : RieszMF.Global.remark_5_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:12:32.682247+00:00
-- url     : https://prove2.me/theorems/67408ad2-32b6-4ecc-afdc-cc0eeb5384b0
-- title:
--   Remark 5.10, (5.32), p. 26 — $F_N\ge-C_p\|\mu\|_{L^\infty}^{s/d}N^{-\lambda/(\lambda+s)}(1+\dots)$ for globally superharmonic $\mathsf g$
-- statement:
--   Let $d\ge3$, $0\le s\le d-2$, and let $\mathsf g$ satisfy (i), (iii) with $r_0=\infty$ (global superharmonicity), (iv) and (vi). Let $d/(s+2)<p\le\infty$ and write $\lambda=\lambda_{s,p}=\frac{2p(d-s)}{dp+2p-d}$. There is $C_p>0$ such that for every $N\ge1$, every pairwise distinct $x_N\in(\mathbb R^d)^N$ and every probability density $\mu\in L^\infty(\mathbb R^d)$ (with $\int\log(1+|x|)\,d\mu<\infty$ if $s=0$),
--
--   $$F_N(x_N,\mu)\ge-C_p\,\|\mu\|_{L^\infty}^{s/d}\,N^{-\frac{\lambda}{\lambda+s}}\Big(1+\big(|\log\|\mu\|_{L^\infty}|+\log N\big)\mathbf 1_{s=0}\Big).$$
--
--   The modulated energy is thus almost nonnegative, with an error whose dependence on $\|\mu\|_{L^\infty}$ is balanced so that it remains integrable in time along the decaying solutions of (1.5).
--
--   **Formalization Note** The remark obtains (5.32) from Proposition 5.8 with $\eta_i$ chosen as in (5.31); that choice must lie in Proposition 5.8's range $\eta_i<2^{-\frac{dp-d+2p}{d(p-1)}}\|\mu\|_{L^\infty}^{-1/d}$. Because $\lambda+s=d\gamma_{s,p}$, the choice (5.31) is $\eta_i=(C_pN)^{-1/(\lambda+s)}\|\mu\|_{L^\infty}^{-1/d}$, which lies in that range for every $N\ge1$ once $C_p$ is large (the remark's "for possibly larger constant $C_p$"). The statement is therefore for every $N\ge1$, as on the page, with $C_p$ chosen after $\mathsf g$ and $p$ and before the data. For $p=\infty$, $\lambda_{s,\infty}=2(d-s)/(d+2)$.
-- source:
--   Rosenzweig & Serfaty, Global-in-time mean-field convergence for singular Riesz-type diffusive flows, arXiv:2108.09878v1, p. 26, Remark 5.10, (5.32); setting of Proposition 5.8, pp. 24–25; (5.21), p. 25

import Mathlib
import Definitions.Def_RieszMF_Global_Setting

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace RieszMF.Global

/-- Remark 5.10 (p. 26), (5.32), in the setting of Proposition 5.8: for `d ≥ 3`, `0 ≤ s ≤ d - 2`,
`g` with (i), (iii) for `r₀ = ∞`, (iv), (vi), and `d/(s+2) < p ≤ ∞`, there is `C_p > 0` such
that for every `N ≥ 1`, pairwise distinct `x_N` and `μ ∈ 𝒫 ∩ L^∞` (with a log moment if
`s = 0`), `F_N(x_N, μ) ≥ -C_p ‖μ‖_{L^∞}^{s/d} N^{-λ/(λ+s)} (1 + (|log ‖μ‖_{L^∞}| + log N) 1_{s=0})`,
`λ = λ_{s,p}`. -/
theorem remark_5_10 :
    ∀ (d : ℕ) (s : ℝ), 3 ≤ d → 0 ≤ s → s ≤ (d : ℝ) - 2 →
    ∀ g : RieszMF.Linear.E d → ℝ, RieszMF.Linear.AssumpI g → GloballySuperharmonic g → RieszMF.Linear.AssumpIV d s g → RieszMF.Linear.AssumpVI d s g →
    ∀ p : ℝ≥0∞, ENNReal.ofReal ((d : ℝ) / (s + 2)) < p →
    ∃ Cp : ℝ, 0 < Cp ∧
    ∀ N : ℕ, 0 < N →
    ∀ x : Fin N → RieszMF.Linear.E d, Pairwise (fun i j => x i ≠ x j) →
    ∀ μ : RieszMF.Linear.E d → ℝ, IsProbDensity μ → (s = 0 → RieszMF.Linear.LogMoment μ) →
      -Cp * supNorm μ ^ (s / d) * (N : ℝ) ^ (-(lam d s p / (lam d s p + s))) *
          (1 + (|Real.log (supNorm μ)| + Real.log N) * (if s = 0 then 1 else 0)) ≤
        RieszMF.Linear.modEnergy N g x μ := by sorry

end RieszMF.Global
