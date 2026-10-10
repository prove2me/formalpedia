-- Prove2me | Theorems.Thm_RieszMF_Global_proposition_5_15
-- name    : RieszMF.Global.proposition_5_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:12:01.495355+00:00
-- url     : https://prove2.me/theorems/c0dc85f3-633e-430d-9e91-44678367937d
-- title:
--   Proposition 5.15, p. 28 — renormalized commutator estimate (5.46) for globally superharmonic $\mathsf g$
-- statement:
--   Let $d\ge3$, $0\le s\le d-2$, and let $\mathsf g$ satisfy assumptions (i)–(vii) and (ix), with (iii) for $r_0=\infty$. There is $C>0$ and, for every $d/(s+2)<p\le\infty$, a constant $C_p>0$ (both depending only on $d,s,\mathsf g$, and $C_p$ also on $p$) such that the following holds. Let $x_N$ be pairwise distinct, $\mu\in L^\infty$ a probability density (with a logarithmic moment if $s=0$), $v$ a vector field with $\|\nabla v\|_{L^\infty}<\infty$, and write $\gamma=\gamma_{s,p}$, $\lambda=\lambda_{s,p}$. For every
--   $$N>\big(2^{\frac{dp-d+p}{p-1}}\|\mu\|_{L^\infty}\big)^{\frac{(s+1)(s+\lambda)}d},$$
--   $$\Big|\int_{(\mathbb R^d)^2\setminus\triangle}(v(x)-v(y))\cdot\nabla\mathsf g(x-y)\,d(\mu_N-\mu)^{\otimes2}\Big|\le C\|\nabla v\|_{L^\infty}\||\nabla|^{s+1-d}\mu\|_{L^\infty}N^{-\frac{s+1+\lambda}{(s+\lambda)(1+s)}}+C\Big(\|\nabla v\|_{L^\infty}+\||\nabla|^{\frac{d-s}2}v\|_{L^{\frac{2d}{d-2-s}}}\mathbf 1_{s<d-2}\Big)\Big(F_N(x_N,\mu)+C_p(1+\|\mu\|_{L^\infty}^{\gamma})N^{-\frac{\lambda}{(s+\lambda)(1+s)}}\big(1+(\log N+|\log\|\mu\|_{L^\infty}|)\mathbf 1_{s=0}\big)\Big),$$
--   where $\mu_N=\frac1N\sum_i\delta_{x_i}$.
--
--   This is the commutator estimate that controls the transport term of the modulated-energy inequality by the modulated energy itself, with a better balance of the norms of $\mu$ than Proposition 5.7.
--
--   **Formalization Note** $\|\nabla v\|_{L^\infty}$ is a Lipschitz constant $K$ of $v$ (if $v$ is not Lipschitz the right side is infinite). $\||\nabla|^{\frac{d-s}2}v\|_{L^q}$, $q=\frac{2d}{d-2-s}$, is the $L^q$ norm of any $w\in L^q$ representing $|\nabla|^{\frac{d-s}2}v$ against Schwartz functions with Fourier transform vanishing near $0$; for $s=d-2$ the term carries the factor $0$ and $w$ is unconstrained. $|\nabla|^{s+1-d}\mu$ is the Riesz potential $\mathcal I_{d-s-1}\mu$ with the constant of (2.3). The page lists "(i) – (vii), (ix)" under the standing assumption of §5.2 that $r_0=\infty$ in (iii); (v) and (vii) keep a finite radius. The threshold on $N$ is the page's; for $p=\infty$ its exponent is the limit $d+1$.
-- source:
--   Rosenzweig & Serfaty, Global-in-time mean-field convergence for singular Riesz-type diffusive flows, arXiv:2108.09878v1, p. 28, Proposition 5.15, (5.46); §5.2, p. 24

import Mathlib
import Definitions.Def_RieszMF_Global_Setting

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace RieszMF.Global

/-- Proposition 5.15 (p. 28), (5.46): for `d ≥ 3`, `0 ≤ s ≤ d - 2` and `g` with (i)–(vii), (ix),
(iii) for `r₀ = ∞`, there is `C > 0` and, for every `d/(s+2) < p ≤ ∞`, `C_p > 0` such that for
every pairwise distinct `x_N`, every `μ ∈ 𝒫 ∩ L^∞` (with a log moment if `s = 0`), every
`K`-Lipschitz vector field `v` (`K` in place of `‖∇v‖_{L^∞}`), every `w = |∇|^{(d-s)/2} v` in
`L^{2d/(d-2-s)}` (when `s < d - 2`) and every `N > (2^{(dp-d+p)/(p-1)} ‖μ‖_{L^∞})^{(s+1)(s+λ)/d}`,
`|∫∫_{△ᶜ} (v(x) - v(y))·∇g(x - y) d(μ_N - μ)^{⊗2}|
  ≤ C K ‖|∇|^{s+1-d} μ‖_{L^∞} N^{-(s+1+λ)/((s+λ)(1+s))}
  + C (K + ‖w‖_{L^{2d/(d-2-s)}} 1_{s<d-2}) (F_N(x_N, μ)
      + C_p (1 + ‖μ‖_{L^∞}^γ) N^{-λ/((s+λ)(1+s))} (1 + (log N + |log ‖μ‖_{L^∞}|) 1_{s=0}))`,
`γ = γ_{s,p}`, `λ = λ_{s,p}`, `|∇|^{s+1-d} μ = 𝓘_{d-s-1} μ`. -/
theorem proposition_5_15 :
    ∀ (d : ℕ) (s : ℝ), 3 ≤ d → 0 ≤ s → s ≤ (d : ℝ) - 2 →
    ∀ (g : RieszMF.Linear.E d → ℝ) (r₀ : ℝ),
      RieszMF.Linear.AssumpI g → RieszMF.Linear.AssumpII g → GloballySuperharmonic g → RieszMF.Linear.AssumpIV d s g → 0 < r₀ →
      RieszMF.Linear.AssumpV g r₀ → RieszMF.Linear.AssumpVI d s g → RieszMF.Linear.AssumpVII s g r₀ → AssumpIX d s g →
    ∃ C : ℝ, 0 < C ∧
    ∀ p : ℝ≥0∞, ENNReal.ofReal ((d : ℝ) / (s + 2)) < p →
    ∃ Cp : ℝ, 0 < Cp ∧
    ∀ N : ℕ, 0 < N →
    ∀ x : Fin N → RieszMF.Linear.E d, Pairwise (fun i j => x i ≠ x j) →
    ∀ μ : RieszMF.Linear.E d → ℝ, IsProbDensity μ → (s = 0 → RieszMF.Linear.LogMoment μ) →
    ∀ (v : RieszMF.Linear.E d → RieszMF.Linear.E d) (K : ℝ≥0), LipschitzWith K v →
    ∀ w : RieszMF.Linear.E d → RieszMF.Linear.E d,
      (s < (d : ℝ) - 2 →
        MemLp w (ENNReal.ofReal (2 * d / ((d : ℝ) - 2 - s))) volume ∧
          IsFracGrad d (((d : ℝ) - s) / 2) v w) →
      ((2 : ℝ) ^ thrExp d p * supNorm μ) ^ ((s + 1) * (s + lam d s p) / d) < (N : ℝ) →
      |RieszMF.Linear.offDiag N (fun a b => inner ℝ (v a - v b) (gradient g (a - b))) x μ| ≤
        C * K * supNorm (RieszMF.Linear.rieszPot d ((d : ℝ) - s - 1) μ) *
            (N : ℝ) ^ (-((s + 1 + lam d s p) / ((s + lam d s p) * (1 + s)))) +
          C * (K + (eLpNorm w (ENNReal.ofReal (2 * d / ((d : ℝ) - 2 - s))) volume).toReal *
              (if s < (d : ℝ) - 2 then 1 else 0)) *
            (RieszMF.Linear.modEnergy N g x μ +
              Cp * (1 + supNorm μ ^ gam d s p) *
                (N : ℝ) ^ (-(lam d s p / ((s + lam d s p) * (1 + s)))) *
                (1 + (Real.log N + |Real.log (supNorm μ)|) * (if s = 0 then 1 else 0))) := by sorry

end RieszMF.Global
