-- Prove2me | Theorems.Thm_RieszMF_Global_lemma_2_3
-- name    : RieszMF.Global.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:11:36.961249+00:00
-- url     : https://prove2.me/theorems/e03d44ef-ebaa-4284-b84b-d7cb1cb910b9
-- title:
--   Lemma 2.3, p. 10 — $\|\mathcal I_s f\|_{L^\infty}\lesssim\|f\|_{L^1}^{1-\theta}\|f\|_{L^p}^{\theta}$ for $p>d/s$
-- statement:
--   Let $d\ge1$, $0<s<d$ and $d/s<p\le\infty$, and let $\mathcal I_s f(x)=c_{d,s}\int_{\mathbb R^d}f(y)|x-y|^{-(d-s)}\,dy$ be the Riesz potential of order $s$. There is a constant $C$, depending only on $d,s,p$, such that for every $f\in L^1(\mathbb R^d)\cap L^p(\mathbb R^d)$ the function $\mathcal I_s f$ is continuous and
--
--   $$\|\mathcal I_s f\|_{L^\infty}\le C\,\|f\|_{L^1}^{1-\theta}\,\|f\|_{L^p}^{\theta},\qquad \theta=\frac{d-s}{d(1-1/p)}.$$
--
--   This interpolation bound is the basic tool for controlling convolutions with derivatives of the potential.
--
--   **Formalization Note** The $L^\infty$ bound is stated pointwise for every $x$, which is equivalent for a continuous function. $1/p=0$ for $p=\infty$.
-- source:
--   Rosenzweig & Serfaty, Global-in-time mean-field convergence for singular Riesz-type diffusive flows, arXiv:2108.09878v1, p. 10, Lemma 2.3, (2.7)

import Mathlib
import Definitions.Def_RieszMF_Global_Setting

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace RieszMF.Global

/-- Lemma 2.3 (p. 10), (2.7): for `d ≥ 1`, `0 < s < d` and `d/s < p ≤ ∞` there is `C` such that
for every `f ∈ L¹ ∩ L^p`, `𝓘_s f` is continuous and
`‖𝓘_s f‖_{L^∞} ≤ C ‖f‖_{L¹}^{1-θ} ‖f‖_{L^p}^θ`, `θ = (d - s)/(d(1 - 1/p))`. -/
theorem lemma_2_3 :
    ∀ (d : ℕ) (s : ℝ), 1 ≤ d → 0 < s → s < (d : ℝ) →
    ∀ p : ℝ≥0∞, ENNReal.ofReal ((d : ℝ) / s) < p →
    ∃ C : ℝ,
    ∀ f : RieszMF.Linear.E d → ℝ, MemLp f 1 volume → MemLp f p volume →
      Continuous (RieszMF.Linear.rieszPot d s f) ∧
      ∀ x : RieszMF.Linear.E d, |RieszMF.Linear.rieszPot d s f x| ≤
        C * (eLpNorm f 1 volume).toReal ^ (1 - ((d : ℝ) - s) / ((d : ℝ) * (1 - p⁻¹.toReal))) *
          (eLpNorm f p volume).toReal ^ (((d : ℝ) - s) / ((d : ℝ) * (1 - p⁻¹.toReal))) := by sorry

end RieszMF.Global
