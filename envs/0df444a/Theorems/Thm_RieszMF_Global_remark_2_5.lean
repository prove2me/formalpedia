-- Prove2me | Theorems.Thm_RieszMF_Global_remark_2_5
-- name    : RieszMF.Global.remark_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:12:52.827981+00:00
-- url     : https://prove2.me/theorems/983d6f09-482c-4dfe-878b-6e8b626f7a51
-- title:
--   Remark 2.5, (2.9), p. 10 — $\|\nabla^{\otimes k}\mathsf g*f\|_{L^\infty}\lesssim\|f\|_{L^1}^{1-(s+k)/d}\|f\|_{L^\infty}^{(s+k)/d}$
-- statement:
--   Let $0\le s<d$ and let $\mathsf g$ satisfy assumption (iv) of order $s$. For every integer $1\le k<d-s$ there is a constant $C$ such that for every $f\in L^1(\mathbb R^d)\cap L^\infty(\mathbb R^d)$ and every $x\in\mathbb R^d$,
--
--   $$\Big|\int_{\mathbb R^d}f(y)\,\nabla^{\otimes k}\mathsf g(x-y)\,dy\Big|\le C\,\|f\|_{L^1}^{1-\frac{s+k}{d}}\,\|f\|_{L^\infty}^{\frac{s+k}{d}}.$$
--
--   The estimate bounds the velocity field $\mathbb M\nabla\mathsf g*\mu$ and its derivatives in terms of the $L^1$ and $L^\infty$ norms of $\mu$.
--
--   **Formalization Note** The tensor-valued convolution is a Bochner integral of `iteratedFDeriv` values with the operator norm; the $L^\infty$ norm is written as a bound at every point. The constant depends on $d,s,k$ and on $\mathsf g$ through (iv).
-- source:
--   Rosenzweig & Serfaty, Global-in-time mean-field convergence for singular Riesz-type diffusive flows, arXiv:2108.09878v1, p. 10, Remark 2.5, (2.9)

import Mathlib
import Definitions.Def_RieszMF_Global_Setting

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace RieszMF.Global

/-- Remark 2.5 (p. 10), (2.9): if `0 ≤ s < d`, `g` satisfies (iv) and `1 ≤ k < d - s` is an
integer, there is `C` such that for every `f ∈ L¹ ∩ L^∞` and every `x`,
`|(∇^{⊗k} g ∗ f)(x)| ≤ C ‖f‖_{L¹}^{1-(s+k)/d} ‖f‖_{L^∞}^{(s+k)/d}`. -/
theorem remark_2_5 :
    ∀ (d : ℕ) (s : ℝ), 0 ≤ s → s < (d : ℝ) →
    ∀ g : RieszMF.Linear.E d → ℝ, RieszMF.Linear.AssumpIV d s g →
    ∀ k : ℕ, 1 ≤ k → (k : ℝ) < (d : ℝ) - s →
    ∃ C : ℝ,
    ∀ f : RieszMF.Linear.E d → ℝ, MemLp f 1 volume → MemLp f ⊤ volume →
    ∀ x : RieszMF.Linear.E d,
      ‖∫ y, f y • iteratedFDeriv ℝ k g (x - y)‖ ≤
        C * (eLpNorm f 1 volume).toReal ^ (1 - (s + k) / (d : ℝ)) *
          (eLpNorm f ⊤ volume).toReal ^ ((s + k) / (d : ℝ)) := by sorry

end RieszMF.Global
