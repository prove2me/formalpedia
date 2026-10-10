-- Prove2me | Theorems.Thm_RieszMF_Linear_proposition_5_7
-- name    : RieszMF.Linear.proposition_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:15:57.360009+00:00
-- url     : https://prove2.me/theorems/bf347797-606e-45c0-9486-8d2118813d88
-- title:
--   Proposition 5.7, p. 24 — renormalized commutator estimate (5.19)
-- statement:
--   Let $d\ge3$, $0\le s\le d-2$, and let $\mathsf g$ satisfy assumptions (i)–(vii) and (ix). There is a constant $C$ depending only on $d$, $s$ and $\mathsf g$ such that the following holds. Let $x_N\in(\mathbb R^d)^N$ be pairwise distinct, $\mu\in\mathcal P(\mathbb R^d)\cap L^\infty(\mathbb R^d)$ (with $\int\log(1+|x|)\,d\mu<\infty$ if $s=0$), and $v$ a vector field on $\mathbb R^d$. Then
--   $$\Big|\int_{(\mathbb R^d)^2\setminus\triangle}(v(x)-v(y))\cdot\nabla\mathsf g(x-y)\,d(\mu_N-\mu)^{\otimes2}(x,y)\Big|\le C\Big(\|\nabla v\|_{L^\infty}+\big\||\nabla|^{\frac{d-s}2}v\big\|_{L^{\frac{2d}{d-2-s}}}\mathbf 1_{s<d-2}\Big)\Big(F_N(x_N,\mu)+CN^{-\frac{s+3}{(s+2)(s+1)}}\||\nabla|^{s+1-d}\mu\|_{L^\infty}+C(1+\|\mu\|_{L^\infty})N^{-\frac2{(s+2)(s+1)}}\big(1+(\log N)(\mathbf 1_{s=0}+\mathbf 1_{s=d-2})\big)\Big).$$
--
--   Applied with $v=u^t=\mathbb M\nabla\mathsf g*\mu^t$, this bounds the transport term in the evolution of $F_N$ by $F_N$ itself plus vanishing errors, which closes the Gronwall argument.
--
--   **Formalization Note.** $\|\nabla v\|_{L^\infty}$ is replaced by any Lipschitz constant $K$ of $v$ (a non-Lipschitz $v$ makes the right side infinite, and the bound is increasing in $K$). $|\nabla|^\alpha=(-\Delta)^{\alpha/2}$ is the Fourier multiplier $(2\pi|\xi|)^\alpha$; $w=|\nabla|^{(d-s)/2}v$ is any $L^{2d/(d-2-s)}$ vector field with $\int w_j\varphi=\int v_j\,\mathcal F^{-1}((2\pi|\xi|)^{(d-s)/2}\widehat\varphi)$ for every Schwartz $\varphi$ whose Fourier transform vanishes near $0$ (required only when $s<d-2$; for $s=d-2$ the term carries the factor $0$). $|\nabla|^{s+1-d}\mu=\mathcal I_{d-s-1}\mu$, and $\|\mu\|_{L^\infty}$ is the essential supremum.
-- source:
--   Rosenzweig & Serfaty, Global-in-time mean-field convergence for singular Riesz-type diffusive flows, arXiv:2108.09878v1, p. 24, Proposition 5.7, (5.19)

import Mathlib
import Definitions.Def_RieszMF_Linear_Setting

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped NNReal ENNReal FourierTransform Laplacian

namespace RieszMF.Linear

theorem proposition_5_7 (d : ℕ) (hd : 3 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s ≤ d - 2)
    (g : E d → ℝ) (r₀ : ℝ) (h1 : AssumpI g) (h2 : AssumpII g) (h3 : AssumpIII g r₀)
    (h4 : AssumpIV d s g) (h5 : AssumpV g r₀) (h6 : AssumpVI d s g) (h7 : AssumpVII s g r₀)
    (h9 : AssumpIX d s g) :
    ∃ C : ℝ, ∀ N : ℕ, 0 < N → ∀ x : Fin N → E d, Pairwise (fun i j => x i ≠ x j) →
      ∀ μ : E d → ℝ, IsProbDensityLinfty μ → (s = 0 → LogMoment μ) →
      ∀ (v : E d → E d) (K : ℝ≥0), LipschitzWith K v →
      ∀ w : E d → E d, (s < d - 2 → IsFracGrad (((d : ℝ) - s) / 2) v w ∧
          MemLp w (ENNReal.ofReal (2 * d / ((d : ℝ) - 2 - s))) volume) →
        |offDiag N (fun a b => inner ℝ (v a - v b) (gradient g (a - b))) x μ|
          ≤ C * ((K : ℝ) + (eLpNorm w (ENNReal.ofReal (2 * d / ((d : ℝ) - 2 - s))) volume).toReal
                * (if s < (d : ℝ) - 2 then 1 else 0))
            * (modEnergy N g x μ
              + C * (N : ℝ) ^ (-((s + 3) / ((s + 2) * (s + 1))))
                * lpNorm (rieszPot d ((d : ℝ) - s - 1) μ) ⊤
              + C * (1 + lpNorm μ ⊤) * (N : ℝ) ^ (-(2 / ((s + 2) * (s + 1))))
                * (1 + Real.log N * ((if s = 0 then 1 else 0) + (if s = (d : ℝ) - 2 then 1 else 0)))) := by sorry

end RieszMF.Linear
