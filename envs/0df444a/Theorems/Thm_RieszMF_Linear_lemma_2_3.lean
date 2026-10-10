-- Prove2me | Theorems.Thm_RieszMF_Linear_lemma_2_3
-- name    : RieszMF.Linear.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:16:01.558209+00:00
-- url     : https://prove2.me/theorems/26ee12b6-ec28-4d20-bd5b-b3c328e1d78c
-- title:
--   Lemma 2.3, p. 10 — $\|\mathcal I_s f\|_{L^\infty}\lesssim\|f\|_{L^1}^{1-\theta}\|f\|_{L^p}^{\theta}$, $\theta=\frac{d-s}{d(1-1/p)}$, and $\mathcal I_s f$ is continuous
-- statement:
--   Let $d\ge1$, $0<s<d$ and $d/s<p\le\infty$. There is a constant $C$, depending only on $d,s,p$, such that for every $f\in L^1(\mathbb R^d)\cap L^p(\mathbb R^d)$ the Riesz potential
--   $$\mathcal I_s f(x)=c_{d,s}\int_{\mathbb R^d}\frac{f(y)}{|x-y|^{d-s}}\,dy$$
--   converges absolutely at every $x$, defines a continuous function, and
--   $$\|\mathcal I_s f\|_{L^\infty}\le C\,\|f\|_{L^1}^{1-\frac{d-s}{d(1-1/p)}}\,\|f\|_{L^p}^{\frac{d-s}{d(1-1/p)}}.$$
--
--   This interpolation bound is how the paper controls velocity fields $\nabla^{\otimes k}\mathsf g*\mu$ by $L^1$ and $L^\infty$ norms of the density.
--
--   **Formalization Note.** The $L^\infty$ bound is stated pointwise at every $x$, which is equivalent for a continuous function; $1/p$ is $0$ for $p=\infty$. The absolute convergence of the defining integral is part of the conclusion, so no default value of a divergent integral enters.
-- source:
--   Rosenzweig & Serfaty, Global-in-time mean-field convergence for singular Riesz-type diffusive flows, arXiv:2108.09878v1, p. 10, Lemma 2.3, (2.7)

import Mathlib
import Definitions.Def_RieszMF_Linear_Setting

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped NNReal ENNReal FourierTransform Laplacian

namespace RieszMF.Linear

theorem lemma_2_3 (d : ℕ) (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 < s) (hsd : s < d)
    (p : ℝ≥0∞) (hp : ENNReal.ofReal ((d : ℝ) / s) < p) :
    ∃ C : ℝ, ∀ f : E d → ℝ, MemLp f 1 volume → MemLp f p volume →
      (∀ x : E d, Integrable (fun y => f y / ‖x - y‖ ^ ((d : ℝ) - s)) volume) ∧
      Continuous (rieszPot d s f) ∧
      ∀ x : E d, |rieszPot d s f x| ≤
        C * lpNorm f 1 ^ (1 - ((d : ℝ) - s) / (d * (1 - (p⁻¹).toReal)))
          * lpNorm f p ^ (((d : ℝ) - s) / (d * (1 - (p⁻¹).toReal))) := by sorry

end RieszMF.Linear
