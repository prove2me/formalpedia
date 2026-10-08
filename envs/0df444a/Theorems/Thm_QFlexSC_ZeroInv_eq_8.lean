-- Prove2me | Theorems.Thm_QFlexSC_ZeroInv_eq_8
-- name    : QFlexSC.ZeroInv.eq_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:57.534827+00:00
-- url     : https://prove2.me/theorems/3c990c11-34e3-4aed-8aa5-cf778bf88bff
-- title:
--   (8), p. 95 — the IR constraints (6) imply the cumulative bounds (1 − Ω_j^out) f_j(t) ≤ f_0(t + j) ≤ (1 + A_j^out) f_j(t)
-- statement:
--   Let $f(t) = [f_0(t), f_1(t), \dots]$ be the release schedules a flex node receives in periods $t = 0, 1, \dots$, and let the output QF parameters satisfy $\alpha^{out}_q \ge 0$ and $0 \le \omega^{out}_q \le 1$ for $q \ge 1$. If every revision obeys the output Incremental Revision constraints (6),
--   $$(1 - \omega^{out}_j) f_j(t) \le f_{j-1}(t+1) \le (1 + \alpha^{out}_j) f_j(t) \qquad (t \ge 0,\ j \ge 1),$$
--   then for all $t \ge 0$ and $j \ge 0$
--   $$(1 - \Omega^{out}_j)\, f_j(t) \le f_0(t+j) \le (1 + A^{out}_j)\, f_j(t),$$
--   where $1 - \Omega^{out}_j = \prod_{q=1}^{j}(1 - \omega^{out}_q)$ and $1 + A^{out}_j = \prod_{q=1}^{j}(1 + \alpha^{out}_q)$.
--
--   These are the Cumulative Flexibility (CF) constraints: the current estimate $f_j(t)$ bounds the actual purchase $f_0(t+j)$ in period $t+j$. They convert the period-to-period revision rules into the bounds the MC policy plans against.
--
--   **Formalization Note.** The paper states (8) for $j \ge 1$; the case $j = 0$ is the trivial identity $f_0(t) \le f_0(t) \le f_0(t)$ and is included. No sign condition on $f$ is needed.
-- source:
--   Tsay & Lovejoy, Quantity flexibility contracts and supply chain performance, MSOM 1(2) (1999), p. 95, (8)–(9)

import Mathlib
import Definitions.Def_QFlexSC_ZeroInv_Model

namespace QFlexSC.ZeroInv

theorem eq_8 (P : QFParams) (f : ℕ → ℕ → ℝ)
    (hstd : ∀ q, 1 ≤ q → 0 ≤ P.αout q ∧ 0 ≤ P.ωout q ∧ P.ωout q ≤ 1)
    (hIR : IROut P f) :
    ∀ t j : ℕ, (1 - Ωcum P.ωout j) * f t j ≤ f (t + j) 0 ∧
      f (t + j) 0 ≤ (1 + Acum P.αout j) * f t j := by sorry

end QFlexSC.ZeroInv
