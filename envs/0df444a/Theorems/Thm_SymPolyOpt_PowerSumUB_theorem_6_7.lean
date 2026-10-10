-- Prove2me | Theorems.Thm_SymPolyOpt_PowerSumUB_theorem_6_7
-- name    : SymPolyOpt.PowerSumUB.theorem_6_7
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-09T07:22:47.876564+00:00
-- url     : https://prove2.me/theorems/4606d7a2-19ba-4a59-bc00-e915f4f80a8d
-- title:
--   Theorem 6.7, p. 27 — min P_nmq ≤ U_nmq, with equality when P_nmq has an optimal solution with at most m non-zero entries
-- statement:
--   Let $n, m, q \in \mathbb{N}$ with $m \le n$ and $m \le q \le 2m - 2$, and let $\gamma_1, \dots, \gamma_{m-1} \in \mathbb{R}$. Let $\min \mathrm{P}_{nmq}$ be the optimal value of
--   $$\mathrm{P}_{nmq}: \quad \min \sum_{i=1}^n x_i^q \quad \text{s.t.} \quad \sum_{i=1}^n x_i^j = \gamma_j, \quad j = 1, \dots, m-1,$$
--   and let $\mathrm{U}_{nmq}$ be the value of the one-variable SDP (6.7): the infimum of $s_q(p) = Q_q(p_0)$ over the monic real polynomials $p$ of degree $m$ with Newton sums $s_j(p) = \gamma_j$ for $j = 1, \dots, m-1$ and $H_m(s(p)) \succeq 0$ (with $s_0 = m$). Then:
--
--   1. $\min \mathrm{P}_{nmq} \le \mathrm{U}_{nmq}$;
--   2. if $\mathrm{P}_{nmq}$ has an optimal solution $x^* \in \mathbb{R}^n$ with at most $m$ non-zero entries, then
--   $$\min \mathrm{P}_{nmq} = \mathrm{U}_{nmq},$$
--   so that $\mathrm{P}_{nmq}$ has the equivalent convex formulation (6.7).
--
--   The theorem complements the Hankel-matrix lower bound of Theorem 6.6 by an upper bound computed from an SDP in the single variable $p_0$, whose size depends on $m$ and not on $n$.
--
--   **Formalization Note** Both values are infima in the extended reals (`EReal`), so no optimal solution of (6.7) is assumed to exist. The hypothesis $m \le q$ is the standing assumption $q \ge m$ of (6.4); with $q \le 2m - 2$ it forces $m \ge 2$. "An optimal solution" is a feasible point whose objective value equals $\min \mathrm{P}_{nmq}$; "at most $m$ non-zero entries" counts the indices $i$ with $x^*_i \ne 0$.
-- source:
--   Riener, Theobald, Jansson Andrén and Lasserre, Exploiting symmetries in SDP-relaxations for polynomial optimization, arXiv:1103.0486v3, p. 27, Theorem 6.7

import Mathlib
import Definitions.Def_SymPolyOpt_PowerSumUB_Setting

namespace SymPolyOpt.PowerSumUB

theorem theorem_6_7 (n m q : ℕ) (γ : ℕ → ℝ) (hmn : m ≤ n) (hmq : m ≤ q)
    (hq : q ≤ 2 * m - 2) :
    SymPolyOpt.PowerSumLB.minP n m q γ ≤ valU m q γ ∧
      ((∃ x ∈ SymPolyOpt.PowerSumLB.feasP n m γ, ((SymPolyOpt.PowerSumLB.powerSum x q : ℝ) : EReal) = SymPolyOpt.PowerSumLB.minP n m q γ ∧
          (Finset.univ.filter (fun i => x i ≠ 0)).card ≤ m) →
        SymPolyOpt.PowerSumLB.minP n m q γ = valU m q γ) := by sorry

end SymPolyOpt.PowerSumUB
