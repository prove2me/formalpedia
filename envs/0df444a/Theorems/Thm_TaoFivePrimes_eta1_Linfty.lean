-- Prove2me | Theorems.Thm_TaoFivePrimes_eta1_Linfty
-- name    : TaoFivePrimes.eta1_Linfty
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-13T22:11:27.827542+00:00
-- url     : https://prove2.me/theorems/b326a4b1-b836-4d64-9761-58f447fbf648
-- title:
--   Tao Section 8: $\|\eta_1\|_{L^\infty(\mathbb{R})} = 1$
-- statement:
--   Throughout, $\eta_1$ is the symmetric trapezoidal cutoff of Section 8 of the source,
--
--   $$\eta_1(t)\;=\;\bigl(1-10\,\operatorname{dist}(t,[0.2,0.8])\bigr)_{+},$$
--
--   which is supported in $[0.1,0.9]$, equals $1$ on $[0.2,0.8]$, and rises and falls linearly with slope $\pm10$ in between.
--
--   Its supremum is $$\|\eta_1\|_{L^\infty(\mathbb R)}=1,$$ attained on the whole plateau $[0.2,0.8]$.
--
--   The source records this together with the other norms of $\eta_1$ for repeated use in Section 8, where they are what is checked against the hypotheses of Corollary 4.9 and against the $L^2$ estimates of the final argument.
--
--   **Formalization Note** The supremum is stated as the conjunction of the bound $\eta_1(t)\le1$ for all $t$ and the attainment $\eta_1(1/2)=1$.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 8, equation (8.3)

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount

open MeasureTheory

theorem TaoFivePrimes.eta1_Linfty :
    (∀ t : ℝ, TaoFivePrimes.eta1 t ≤ 1) ∧ TaoFivePrimes.eta1 (1/2) = 1 := by sorry
