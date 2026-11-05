-- Prove2me | Theorems.Thm_StrongConv_abs_nu_le
-- name    : StrongConv.abs_nu_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T22:45:48.304557+00:00
-- url     : https://prove2.me/theorems/a581829f-b164-40ac-8a3b-c99aded555b8
-- title:
--   Corollary 6.2 — bounds on the expansion coefficients νₘ
-- statement:
--   Let $P$ be self-adjoint of degree at most $q_0$, with $q_0 \ge 1$, and let $K = \|P\|_{\mathrm M_D(\mathbb C)\otimes C^*(\mathbf F_d)}$. Then for every $m \ge 0$, $q \ge 1$ and every real polynomial $h$ of degree at most $q$, the $m$-th expansion coefficient (`nu P m`) satisfies
--   $$|\nu_m(h)| \le (4qq_0(1 + \log d))^{4m}\,\sup_{x\in[-K,K]} |h(x)|.$$
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 21, Corollary 6.2

import Mathlib
import Definitions.Def_StrongConv

open Polynomial

namespace StrongConv

theorem abs_nu_le {D d q₀ : ℕ} (P : NCPoly D d) (hP : P.IsSelfAdjoint) (hq₀ : P.degree ≤ q₀)
    (hq₀' : 1 ≤ q₀) (m q : ℕ) (hq : 1 ≤ q) (h : ℝ[X]) (hh : h.natDegree ≤ q) :
    |nu P m h| ≤ (4 * q * q₀ * (1 + Real.log d)) ^ (4 * m) *
      cNorm 0 (fun x => h.eval x) (-P.fullNorm) P.fullNorm := by
  sorry

end StrongConv
