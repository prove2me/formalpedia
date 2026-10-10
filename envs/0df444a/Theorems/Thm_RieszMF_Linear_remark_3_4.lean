-- Prove2me | Theorems.Thm_RieszMF_Linear_remark_3_4
-- name    : RieszMF.Linear.remark_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:15:55.073087+00:00
-- url     : https://prove2.me/theorems/6a3c432b-19bd-459d-91e3-2519ffba1cf1
-- title:
--   Remark 3.4, p. 12 — $L^p$ norms of solutions of (1.5) are nonincreasing in time
-- statement:
--   Let $d\ge3$, $0\le s<d-2$, $\sigma>0$, let $\mathbb M$ satisfy $\mathbb M\xi\cdot\xi\le0$ and let $\mathsf g$ be an admissible potential with radius $r_0$.
--   Let $\mu\in C([0,\infty);L^1\cap L^\infty)$ be a mild solution (3.1) of
--   $$\partial_t\mu=-\operatorname{div}(\mu\,\mathbb M\nabla\mathsf g*\mu)+\sigma\Delta\mu,\qquad\mu|_{t=0}=\mu^0,$$
--   and, if $\mathbb M:\nabla^{\otimes2}\mathsf g$ does not vanish identically on $\mathbb R^d\setminus\{0\}$, assume $\mu^t\ge0$ for all $t$. Then for every $1\le p\le\infty$ and $0\le t'\le t$,
--   $$\|\mu^t\|_{L^p}\le\|\mu^{t'}\|_{L^p}.$$
--
--   In particular $\sup_t\|\mu^t\|_{L^\infty}=\|\mu^0\|_{L^\infty}$, which is why the constants of the main theorem depend only on the initial density.
--
--   **Formalization Note.** The remark is printed for $\mu\in C([0,T];X)$ without a sign condition. Its proof (3.19) uses assumption (x) through $(\mathbb M:\nabla^{\otimes2}\mathsf g)*\mu^t\ge0$, which needs $\mu\ge0$ unless $\mathbb M:\nabla^{\otimes2}\mathsf g\equiv0$; the sign hypothesis is Proposition 3.8's. The statement is made for global solutions on $[0,\infty)$; by uniqueness (Proposition 3.1) a solution on $[0,T]$ is the restriction of the global one.
-- source:
--   Rosenzweig & Serfaty, Global-in-time mean-field convergence for singular Riesz-type diffusive flows, arXiv:2108.09878v1, p. 12, Remark 3.4

import Mathlib
import Definitions.Def_RieszMF_Linear_Setting

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped NNReal ENNReal FourierTransform Laplacian

namespace RieszMF.Linear

theorem remark_3_4 (d : ℕ) (hd : 3 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d - 2)
    (σ : ℝ) (hσ : 0 < σ) (M : Matrix (Fin d) (Fin d) ℝ) (hM : NegSemidef M)
    (g : E d → ℝ) (r₀ : ℝ) (hg : Admissible d s M g r₀)
    (μ0 : E d → ℝ) (μ : ℝ≥0 → E d → ℝ) (hμ : IsMildSolution d σ M g μ0 μ)
    (hsign : (∃ x : E d, x ≠ 0 ∧ frob M g x ≠ 0) → ∀ t, ∀ᵐ x ∂volume, 0 ≤ μ t x)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (t' t : ℝ≥0) (htt : t' ≤ t) :
    eLpNorm (μ t) p volume ≤ eLpNorm (μ t') p volume := by sorry

end RieszMF.Linear
