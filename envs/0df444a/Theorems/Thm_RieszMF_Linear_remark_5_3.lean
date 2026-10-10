-- Prove2me | Theorems.Thm_RieszMF_Linear_remark_5_3
-- name    : RieszMF.Linear.remark_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:15:52.968057+00:00
-- url     : https://prove2.me/theorems/3c347450-3a63-464c-babc-29fb8fc1e173
-- title:
--   Remark 5.3, (5.11), p. 22 — smeared lower bound for $F_N$ when only $\hat{\mathsf g}\ge0$ on $\mathbb R^d\setminus\{0\}$
-- statement:
--   Let $d\ge3$, $0\le s\le d-2$, and let $h:\mathbb R^d\to\mathbb R$ satisfy assumptions (iii) and (iv) at order $s$ and, instead of (vi), only $\hat h\ge0$ on $\mathbb R^d\setminus\{0\}$ (Fourier transform away from the origin). There is a constant $C>0$ such that for every $N\ge1$, every pairwise distinct $x_N\in(\mathbb R^d)^N$, every $\mu\in\mathcal P(\mathbb R^d)\cap L^\infty(\mathbb R^d)$ (with finite log moment if $s=0$) and every choice of $0<\eta_1,\dots,\eta_N<\min\{\frac12,\frac{r_0}2\}$,
--   $$\frac1{N^2}\sum_{\substack{1\le i\ne j\le N\\|x_i-x_j|\le r_0/2}}\big(h(x_j-x_i)-h_{\eta_i}(x_j-x_i)\big)_+\le F_N(x_N,\mu)+\frac CN\sum_{i=1}^N\Big(\Big(\eta_i^2+\frac{\eta_i^{-s}(1+|\log\eta_i|\mathbf 1_{s=0})}N\Big)+C\|\mu\|_{L^\infty}\eta_i^{d-s}\big(1+|\log\eta_i|(\mathbf 1_{s=0}+\mathbf 1_{s=d-2})\big)\Big),$$
--   where $F_N$ is the modulated energy of $h$ and $h_\eta$ is the average of $h$ over spheres of radius $\eta$.
--
--   Corollary 5.6 applies this to $h=-\Delta\mathsf g$, a potential of order $s+2$, to show the diffusion term is almost nonpositive.
--
--   **Formalization Note.** The statement is for a generic potential $h$ of order $s$, as Corollary 5.6 uses it with $s+2$ in place of $s$. $\hat h\ge0$ means: some function $\hat h\ge0$ on $\xi\ne0$ satisfies $\int h\,\widehat\varphi=\int\hat h\,\varphi$ for all Schwartz $\varphi$ vanishing near $0$.
-- source:
--   Rosenzweig & Serfaty, Global-in-time mean-field convergence for singular Riesz-type diffusive flows, arXiv:2108.09878v1, p. 22, Remark 5.3, (5.11)

import Mathlib
import Definitions.Def_RieszMF_Linear_Setting

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped NNReal ENNReal FourierTransform Laplacian

namespace RieszMF.Linear

theorem remark_5_3 (d : ℕ) (hd : 3 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s ≤ d - 2)
    (h : E d → ℝ) (r₀ : ℝ) (h3 : AssumpIII h r₀) (h4 : AssumpIV d s h)
    (h6 : ∃ ĥ : E d → ℝ, (∀ ξ : E d, ξ ≠ 0 → 0 ≤ ĥ ξ) ∧ FTOffZero h ĥ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ x : Fin N → E d, Pairwise (fun i j => x i ≠ x j) →
      ∀ μ : E d → ℝ, IsProbDensityLinfty μ → (s = 0 → LogMoment μ) →
      ∀ η : Fin N → ℝ, (∀ i, 0 < η i ∧ η i < min (1 / 2) (r₀ / 2)) →
        (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ (Finset.univ.erase i).filter (fun j => ‖x i - x j‖ ≤ r₀ / 2),
            max (h (x j - x i) - smear h (η i) (x j - x i)) 0
          ≤ modEnergy N h x μ
            + (C / N) * ∑ i, ((η i ^ 2 + η i ^ (-s) * (1 + |Real.log (η i)| * (if s = 0 then 1 else 0)) / N)
              + C * lpNorm μ ⊤ * η i ^ ((d : ℝ) - s)
                * (1 + |Real.log (η i)| * ((if s = 0 then 1 else 0) + (if s = (d : ℝ) - 2 then 1 else 0)))) := by sorry

end RieszMF.Linear
