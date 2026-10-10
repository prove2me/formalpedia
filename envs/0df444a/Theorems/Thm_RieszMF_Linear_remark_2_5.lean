-- Prove2me | Theorems.Thm_RieszMF_Linear_remark_2_5
-- name    : RieszMF.Linear.remark_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:15:50.862868+00:00
-- url     : https://prove2.me/theorems/a4188c78-d527-48d1-8bff-57116ac286ac
-- title:
--   Remark 2.5, (2.9), p. 10 — $\|\nabla^{\otimes k}\mathsf g*f\|_{L^\infty}\lesssim\|f\|_{L^1}^{1-\frac{s+k}d}\|f\|_{L^\infty}^{\frac{s+k}d}$ for $1\le k<d-s$
-- statement:
--   Let $d\ge1$, $0\le s<d$, and let $\mathsf g$ satisfy assumption (iv) at order $s$: $\mathsf g$ is smooth off the origin and $|\nabla^{\otimes k}\mathsf g(x)|\le C_k(|x|^{-(s+k)}+|\log|x||\mathbf 1_{s=k=0})$. For every integer $1\le k<d-s$ there is a constant $C$ such that for every $f\in L^1(\mathbb R^d)\cap L^\infty(\mathbb R^d)$ and every $x$, the tensor-valued convolution $\nabla^{\otimes k}\mathsf g*f(x)=\int\nabla^{\otimes k}\mathsf g(x-y)f(y)\,dy$ converges absolutely and
--   $$|\nabla^{\otimes k}\mathsf g*f(x)|\le C\,\|f\|_{L^1}^{1-\frac{s+k}{d}}\,\|f\|_{L^\infty}^{\frac{s+k}{d}}.$$
--
--   The case $k=1$ bounds the velocity $\mathbb M\nabla\mathsf g*\mu$ and $k=2$ its gradient; both bounds are used throughout the Gronwall argument.
--
--   **Formalization Note.** The $L^\infty$ norm is written as a bound at every point, which is equivalent since the bound is uniform. $C$ may depend on $d,s,k$ and on $\mathsf g$ through the constants of (iv).
-- source:
--   Rosenzweig & Serfaty, Global-in-time mean-field convergence for singular Riesz-type diffusive flows, arXiv:2108.09878v1, p. 10, Remark 2.5, (2.9)

import Mathlib
import Definitions.Def_RieszMF_Linear_Setting

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped NNReal ENNReal FourierTransform Laplacian

namespace RieszMF.Linear

theorem remark_2_5 (d : ℕ) (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (g : E d → ℝ) (hg : AssumpIV d s g) (k : ℕ) (hk : 1 ≤ k) (hkd : (k : ℝ) < d - s) :
    ∃ C : ℝ, ∀ f : E d → ℝ, MemLp f 1 volume → MemLp f ⊤ volume → ∀ x : E d,
      Integrable (fun y => f y • iteratedFDeriv ℝ k g (x - y)) volume ∧
      ‖∫ y, f y • iteratedFDeriv ℝ k g (x - y)‖ ≤
        C * lpNorm f 1 ^ (1 - (s + k) / d) * lpNorm f ⊤ ^ ((s + k) / d) := by sorry

end RieszMF.Linear
