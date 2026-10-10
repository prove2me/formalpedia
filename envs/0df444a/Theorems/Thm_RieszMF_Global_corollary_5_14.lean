-- Prove2me | Theorems.Thm_RieszMF_Global_corollary_5_14
-- name    : RieszMF.Global.corollary_5_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:11:42.285515+00:00
-- url     : https://prove2.me/theorems/8bf4a48b-5e93-4d06-a189-e655f71b0297
-- title:
--   Corollary 5.14, p. 28 — lower bounds (5.44)–(5.45) for $\iint(-\Delta\mathsf g)\,d(\mu_N-\mu)^{\otimes2}$
-- statement:
--   Let $d\ge3$, $0\le s<d-2$, and let $\mathsf g$ satisfy (i), (iii) with $r_0=\infty$, (iv), (vi), and (viii) with $r_0=\infty$ (that is, when $d-4<s$, an extension $\mathsf G$ of $-\Delta\mathsf g$ with (1.14)–(1.17) on all of $\mathbb R^{d+m}$). Write
--   $$\mathcal W(x_N,\mu)=\int_{(\mathbb R^d)^2\setminus\triangle}(-\Delta\mathsf g)(x-y)\,d\Big(\frac1N\sum_{i=1}^N\delta_{x_i}-\mu\Big)^{\otimes2}(x,y).$$
--
--   1. If $0\le s\le d-4$, then for every $d/(s+4)<p\le\infty$ there is $C_p>0$ such that
--   $$\mathcal W(x_N,\mu)\ge-C_p\|\mu\|_{L^\infty}^{\frac{s+2}d}N^{-\frac{\lambda_{s+2,p}}{\lambda_{s+2,p}+s+2}}.$$
--   2. If $d-4<s<d-2$, there is $C>0$ such that
--   $$\mathcal W(x_N,\mu)\ge-C\|\mu\|_{L^\infty}^{\frac{s+2}d}N^{-\frac{d-s-2}d}.$$
--
--   Both hold for every $N\ge1$, every pairwise distinct $x_N$ and every probability density $\mu\in L^\infty$. Here $\lambda_{s+2,p}$ is (5.21) with $s+2$ in place of $s$.
--
--   The corollary controls the diffusion term of the modulated-energy inequality (Proposition 6.3), with a dependence on $\|\mu\|_{L^\infty}$ that is integrable in time along decaying solutions.
--
--   **Formalization Note** The hypotheses are exactly those listed on the page; no superharmonicity of $-\Delta\mathsf g$ is assumed.
-- source:
--   Rosenzweig & Serfaty, Global-in-time mean-field convergence for singular Riesz-type diffusive flows, arXiv:2108.09878v1, p. 28, Corollary 5.14, (5.44)–(5.45)

import Mathlib
import Definitions.Def_RieszMF_Global_Setting

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace RieszMF.Global

/-- Corollary 5.14 (p. 28): for `d ≥ 3`, `0 ≤ s < d - 2` and `g` with (i), (iii), (iv), (vi),
(viii) for `r₀ = ∞`, with `W(x_N, μ) = ∫∫_{△ᶜ} (-Δg)(x - y) d(μ_N - μ)^{⊗2}`:
(5.44) if `0 ≤ s ≤ d - 4`, for every `d/(s+4) < p ≤ ∞` there is `C_p` with
`W ≥ -C_p ‖μ‖_{L^∞}^{(s+2)/d} N^{-λ_{s+2,p}/(λ_{s+2,p}+s+2)}`;
(5.45) if `d - 4 < s < d - 2`, there is `C` with `W ≥ -C ‖μ‖_{L^∞}^{(s+2)/d} N^{-(d-s-2)/d}`;
for every pairwise distinct `x_N` and every `μ ∈ 𝒫 ∩ L^∞`. -/
theorem corollary_5_14 :
    ∀ (d : ℕ) (s : ℝ), 3 ≤ d → 0 ≤ s → s < (d : ℝ) - 2 →
    ∀ g : RieszMF.Linear.E d → ℝ, RieszMF.Linear.AssumpI g → GloballySuperharmonic g → RieszMF.Linear.AssumpIV d s g → RieszMF.Linear.AssumpVI d s g →
      ((d : ℝ) - 4 < s → HasExtensionGlobal d s g) →
    (s ≤ (d : ℝ) - 4 →
      ∀ p : ℝ≥0∞, ENNReal.ofReal ((d : ℝ) / (s + 4)) < p →
      ∃ Cp : ℝ, 0 < Cp ∧
      ∀ N : ℕ, 0 < N →
      ∀ x : Fin N → RieszMF.Linear.E d, Pairwise (fun i j => x i ≠ x j) →
      ∀ μ : RieszMF.Linear.E d → ℝ, IsProbDensity μ →
        -Cp * supNorm μ ^ ((s + 2) / d) *
            (N : ℝ) ^ (-(lam d (s + 2) p / (lam d (s + 2) p + s + 2))) ≤
          RieszMF.Linear.offDiag N (fun a b => -lap g (a - b)) x μ) ∧
    ((d : ℝ) - 4 < s →
      ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, 0 < N →
      ∀ x : Fin N → RieszMF.Linear.E d, Pairwise (fun i j => x i ≠ x j) →
      ∀ μ : RieszMF.Linear.E d → ℝ, IsProbDensity μ →
        -C * supNorm μ ^ ((s + 2) / d) * (N : ℝ) ^ (-(((d : ℝ) - s - 2) / d)) ≤
          RieszMF.Linear.offDiag N (fun a b => -lap g (a - b)) x μ) := by sorry

end RieszMF.Global
