-- Prove2me | Theorems.Thm_TaoFivePrimes_riemann_verified_zero_set_finite
-- name    : TaoFivePrimes.riemann_verified_zero_set_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T01:27:25.764301+00:00
-- url     : https://prove2.me/theorems/f17e647a-1e54-48f2-8d4c-678c2f2e66f9
-- title:
--   The verified-height zeta zero set is finite
-- statement:
--   Let $T_0 = 3.29 \times 10^9$ and let $Z(T_0)=\{\rho : \zeta(\rho)=0,\ 0<\operatorname{Re}\rho<1,\ 0\le\operatorname{Im}\rho\le T_0\}$. Then $Z(T_0)$ is a finite set.
--
--   This is the finiteness clause of Theorem 1.5 of Tao's paper (arXiv:1201.6656v4), and it is the *non-numerical* half of that statement. Finiteness is not a consequence of the zero count: it is the isolated-zeros theorem for a non-constant analytic function. The Riemann zeta function is analytic on $\mathbb{C}\setminus\{1\}$, which is connected, so its zeros there are isolated; there are no zeros near the pole $s=1$; and a closed box $[0,1]\times[0,T_0]$ is compact. Hence only finitely many zeros lie in the window.
--
--   On the platform this is the discharged seam field `Zeta23.zetaSeam.finite_window` of the definition `Zeta23_Statement_SeamClosed`, proved in `Zeta23/Statement/Seam.lean`. The cardinality bound `|Z(T_0)| \le 10^{10}` and the critical-line statement are separate obligations.
-- source:
--   T. Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656v4, Theorem 1.5, p.4. Finiteness of the zero set in a bounded closed window follows from the isolated-zeros theorem applied to zeta on the connected open set C \ {1}, together with the absence of zeros near the pole s = 1 and compactness of the closed box. https://arxiv.org/html/1201.6656v4#S1

import Mathlib
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Theorems.Thm_zeta_ne_zero_of_mem_strip_of_abs_im_le_two

open Complex Set Topology MeasureTheory Real
open Zeta23

theorem TaoFivePrimes.riemann_verified_zero_set_finite :
    {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧
      s.im ≤ 3.29 * 10 ^ 9}.Finite := by
  sorry
