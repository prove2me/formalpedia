-- Prove2me | Theorems.Thm_TaoFivePrimes_norm_stronglyMajorCutoffModel_eta0_le_one
-- name    : TaoFivePrimes.norm_stronglyMajorCutoffModel_eta0_le_one
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-13T21:05:53.963206+00:00
-- url     : https://prove2.me/theorems/d89225ea-73ce-4cb4-ab68-8aa49babecc4
-- title:
--   The Fourier transform of $\eta_0$ is bounded by its mass
-- statement:
--   Let $\eta_0$ be the cutoff of unit mass supported in $[1/4,1]$ introduced in Section 1 of the source,
--
--   $$\eta_0(t)=4\bigl(\log 2-|\log 2t|\bigr)_{+},\qquad \int_{\mathbb R}\eta_0=1,$$
--
--   and let $\widehat{\eta_0}$ be its Fourier transform in the convention of Section 7,
--
--   $$\widehat{\eta_0}(\xi)=\int_{\mathbb R}\eta_0(t)\,e(\xi t)\,dt,\qquad e(u)=e^{2\pi i u}.$$
--
--   Then, for every real scale $s$ and every frequency $\alpha\in\mathbb R/\mathbb Z$,
--
--   $$\bigl|\widehat{\eta_0}(s\,\alpha)\bigr|\;\le\;1 ,$$
--
--   where $\alpha$ is evaluated at its representative in $(-\tfrac12,\tfrac12]$.
--
--   This is the trivial bound $\|\widehat{\eta_0}\|_{L^\infty}\le\|\eta_0\|_{L^1}=1$ for the main term of the strongly major arc estimate. It is what lets the main term of Proposition 7.2 be discarded at no cost wherever only an upper bound is needed, in particular in the weakly major arc analysis of Section 8.
--
--   **Formalization Note** The frequency is a point of the additive circle $\mathbb R/\mathbb Z$; the Fourier transform is evaluated at the scaled centred representative in $(-\tfrac12,\tfrac12]$, which is the convention of the paper's major arc analysis.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 1, equation (1.7) (definition of $\eta_0$) and Section 5, equation (5.7); the bound $\|\hat\eta_0\|_{L^\infty}\le\|\eta_0\|_{L^1}$ used in Section 7 and Section 8

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount
import Definitions.Def_TaoFivePrimes_stronglyMajorCutoffModel

open MeasureTheory

theorem TaoFivePrimes.norm_stronglyMajorCutoffModel_eta0_le_one (scale : ℝ)
    (alpha : AddCircle (1 : ℝ)) :
    ‖TaoFivePrimes.stronglyMajorCutoffModel TaoFivePrimes.eta0 scale alpha‖ ≤ 1 := by sorry
