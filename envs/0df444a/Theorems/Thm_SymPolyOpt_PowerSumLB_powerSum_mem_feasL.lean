-- Prove2me | Theorems.Thm_SymPolyOpt_PowerSumLB_powerSum_mem_feasL
-- name    : SymPolyOpt.PowerSumLB.powerSum_mem_feasL
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:27:13.640495+00:00
-- url     : https://prove2.me/theorems/76fe02f2-a5bb-4790-be85-2793d6d8c98a
-- title:
--   Proof of Theorem 6.6(a), p. 26 — the power sums of a feasible point of (6.4) are feasible for (6.5)
-- statement:
--   Let $n, m \in \mathbb N$ and $\gamma_1,\dots,\gamma_{m-1} \in \mathbb R$. If $x \in \mathbb R^n$ satisfies $s_j(x) = \gamma_j$ for $j = 1,\dots,m-1$, then its power-sum sequence $s(x) = (s_0(x), s_1(x), \dots)$ is feasible for the semidefinite program (6.5):
--   $$H_n(s(x)) \succeq 0, \qquad s_0(x) = n, \qquad s_j(x) = \gamma_j \ (j = 1,\dots,m-1).$$
--
--   This is the inclusion behind Theorem 6.6(a): every feasible point of the polynomial problem gives a feasible point of the SDP with the same objective value $s_q$. The substantive part is the positive semidefiniteness of the Hankel matrix of power sums of a real point.
-- source:
--   Riener, Theobald, Jansson Andrén and Lasserre, Exploiting symmetries in SDP-relaxations for polynomial optimization, arXiv:1103.0486v3, p. 26, proof of Theorem 6.6(a)

import Mathlib
import Definitions.Def_SymPolyOpt_PowerSumLB_Setting

namespace SymPolyOpt.PowerSumLB

/-- The power-sum vector of every feasible point of (6.4) is feasible for the SDP (6.5). -/
theorem powerSum_mem_feasL (n m : ℕ) (γ : ℕ → ℝ) :
    ∀ x ∈ feasP n m γ, powerSum x ∈ feasL n m γ := by sorry

end SymPolyOpt.PowerSumLB
