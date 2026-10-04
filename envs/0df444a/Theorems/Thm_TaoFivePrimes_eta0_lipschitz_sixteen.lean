-- Prove2me | Theorems.Thm_TaoFivePrimes_eta0_lipschitz_sixteen
-- name    : TaoFivePrimes.eta0_lipschitz_sixteen
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-13T21:13:30.338824+00:00
-- url     : https://prove2.me/theorems/d91a8a80-eae5-4b35-a413-44a1362f1238
-- title:
--   Tao equation (s1-4): the cutoff $\eta_0$ is $16$-Lipschitz
-- statement:
--   Throughout, $\eta_0$ is the Lipschitz cutoff of unit mass supported in $[1/4,1]$ introduced in Section 1 of the source,
--
--   $$\eta_0(t)\;=\;4\bigl(\log 2-|\log 2t|\bigr)_{+},\qquad (u)_{+}=\max(0,u).$$
--
--   It is Lipschitz with constant $$\|\eta_0'\|_{L^\infty(\mathbb R)}=16,$$ that is, $|\eta_0(s)-\eta_0(t)|\le 16|s-t|$ for all real $s,t$; the constant is attained on the rising branch, where the slope is $4/t$ at $t=1/4$.
--
--   The source records this together with the other norms of $\eta_0$ for repeated use in the minor-arc estimates of Sections 5 and 6, where each of them enters an explicit constant.
--
--   **Formalization Note** Because $\eta_0$ has corners, the sup-norm of its derivative is stated in the equivalent form of a Lipschitz bound with constant $16$, which is how it is used.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 5, equation (5.10)

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount

theorem TaoFivePrimes.eta0_lipschitz_sixteen :
    LipschitzWith 16 TaoFivePrimes.eta0 := by sorry
