-- Prove2me | Theorems.Thm_QFlexSC_ZeroInv_proj_succ_eq_zero
-- name    : QFlexSC.ZeroInv.proj_succ_eq_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:50.822057+00:00
-- url     : https://prove2.me/theorems/7b0c286a-f9d7-4f8e-a90d-1ceed047f4e1
-- title:
--   Appendix 1, proof of Proposition 2, p. 108 — if l_{j−1}(t) = 0 and r_{j−1}(t) = f_{j−1}(t) then l_j(t) = 0
-- statement:
--   Fix one period of the Minimum Commitment (MC) policy (21)–(23): data $I(t-1)$, $r(t-1)$, $f(t)$, and the resulting projections $l_j(t)$ and schedule $r_j(t)$. Assume $\alpha^{out}_q \ge 0$ and $0 \le \omega^{in}_q \le 1$ for $q \ge 1$. Let $j \ge 0$ with $f_j(t) \ge 0$. If
--   $$l_j(t) = 0 \qquad\text{and}\qquad r_j(t) = f_j(t),$$
--   then
--   $$l_{j+1}(t) = \bigl[l_j(t) + (1 - \Omega^{in}_j) r_j(t) - (1 + A^{out}_j) f_j(t)\bigr]^+ = \bigl[-(\Omega^{in}_j + A^{out}_j) f_j(t)\bigr]^+ = 0 .$$
--
--   This is the induction step on $j$ in the equal-profile case of Proposition 2: once the projected inventory vanishes and the schedule is passed through unchanged at index $j$, the projected inventory at index $j+1$ vanishes as well.
--
--   **Formalization Note.** The paper's step from index $j-1$ to $j$ is written here from $j$ to $j+1$. No equality of the input and output profiles is assumed: the step uses only $r_j(t) = f_j(t)$, $f_j(t) \ge 0$, $\Omega^{in}_j \ge 0$ and $A^{out}_j \ge 0$. Parameter index $0$ is unused.
-- source:
--   Tsay & Lovejoy, Quantity flexibility contracts and supply chain performance, MSOM 1(2) (1999), p. 108, Appendix 1, proof of Proposition 2

import Mathlib
import Definitions.Def_QFlexSC_ZeroInv_Model

namespace QFlexSC.ZeroInv

theorem proj_succ_eq_zero (P : QFParams) (Iprev : ℝ) (rprev f : ℕ → ℝ) (j : ℕ)
    (hstd : ∀ q, 1 ≤ q → 0 ≤ P.αout q ∧ 0 ≤ P.ωin q ∧ P.ωin q ≤ 1)
    (hf : 0 ≤ f j)
    (hl : proj P Iprev rprev f j = 0)
    (hr : mcStep P Iprev rprev f j = f j) :
    proj P Iprev rprev f (j + 1) = 0 := by sorry

end QFlexSC.ZeroInv
