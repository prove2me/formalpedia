-- Prove2me | Theorems.Thm_TaoFivePrimes_eta0_Linfty_eq_four_log_two
-- name    : TaoFivePrimes.eta0_Linfty_eq_four_log_two
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-13T21:10:47.934837+00:00
-- url     : https://prove2.me/theorems/1723bfac-1c61-4674-8643-aebb8ba8c2b9
-- title:
--   Tao equation (s1-2): the sup norm of the cutoff $\eta_0$ is $4\log 2$
-- statement:
--   Throughout, $\eta_0$ is the Lipschitz cutoff of unit mass supported in $[1/4,1]$ introduced in Section 1 of the source,
--
--   $$\eta_0(t)\;=\;4\bigl(\log 2-|\log 2t|\bigr)_{+},\qquad (u)_{+}=\max(0,u).$$
--
--   Its supremum is $$\|\eta_0\|_{L^\infty(\mathbb R)}=4\log 2,$$ attained at $t=\tfrac12$.
--
--   The source records this together with the other norms of $\eta_0$ for repeated use in the minor-arc estimates of Sections 5 and 6, where each of them enters an explicit constant.
--
--   **Formalization Note** The supremum is stated as the conjunction of the bound $\eta_0(t)\le 4\log 2$ for all $t$ and the attainment $\eta_0(1/2)=4\log 2$, which together characterise it without invoking an essential supremum.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 5, equation (5.8)

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount

theorem TaoFivePrimes.eta0_Linfty_eq_four_log_two :
    (∀ t : ℝ, TaoFivePrimes.eta0 t ≤ 4 * Real.log 2)
      ∧ TaoFivePrimes.eta0 (1/2) = 4 * Real.log 2 := by sorry
