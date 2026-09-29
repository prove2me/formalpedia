-- Prove2me | Theorems.Thm_StochasticProg_ValueOfInfo_prop7_ws_le_spev_le_rp
-- name    : StochasticProg.ValueOfInfo.prop7_ws_le_spev_le_rp
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T04:52:41.807318+00:00
-- url     : https://prove2.me/theorems/64b2ed33-2251-4763-b7aa-0471a1bbb20f
-- title:
--   Chapter 4, Proposition 7 — WS ≤ SPEV ≤ RP
-- statement:
--   This is Chapter 4, Proposition 7 (p. 173) of Birge & Louveaux, *Introduction to Stochastic
--   Programming*.
--
--   Let $I$ be a two-stage stochastic program with fixed recourse and finitely many scenarios
--   (an `Instance`). Fix a reference scenario $\xi^r \in \mathbb R^d$ (not necessarily one of the
--   $K$ possible scenarios); let $p_r = \Pr(\xi=\xi^r) = \sum_{k:\,\xi^k=\xi^r} p_k$ be its own
--   probability under $I$'s scenario distribution, and assume $p_r < 1$.
--
--   The conclusion is the chain
--   $$
--   WS \le SPEV \le RP,
--   $$
--   where $WS$ is the wait-and-see value, $RP$ the recourse problem's optimal value, and $SPEV$
--   the sum of pairs expected values: for each scenario $\xi^k \ne \xi^r$, the *pairs subproblem*
--   of $\xi^r$ and $\xi^k$ has optimal value
--   $\min_{x\in K_1}[p_r\,z(x,\xi^r)+(1-p_r)\,z(x,\xi^k)]$, treating $\{\xi^r,\xi^k\}$ as a
--   two-point distribution with weights $p_r,1-p_r$; $SPEV$ averages these optimal values over the
--   scenarios other than $\xi^r$ itself, weighted by $p_k$ and rescaled by $(1-p_r)^{-1}$, using
--   $\sum_{k:\,\xi^k\ne\xi^r} p_k = 1-p_r$.
--
--   $SPEV$ is computable from at most $K$ two-scenario linear programs, far cheaper than the full
--   $K$-scenario recourse problem $RP$, so this proposition certifies $SPEV$ as a genuine
--   (cheaper) lower bound refinement toward $RP$, sitting strictly between $WS$ and $RP$.
--
--   **Formalization Note** All quantities take values in the extended reals $\overline{\mathbb
--   R}$, combined throughout by the book's own $+\infty$-dominates convention (p. 164), not
--   Mathlib's `EReal` arithmetic. The reference probability $p_r$ is not a free parameter but is
--   computed from $I$ and $\xi^r$ as `refProb I xir`; the hypothesis $p_r < 1$ matches the book's
--   requirement that the factor $(1-p_r)^{-1}$ in $SPEV$'s definition be well-defined and that
--   some other scenario be possible.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, p. 173, Chapter 4, Proposition 7

import Mathlib
import Definitions.Def_StochasticProg_ValueOfInfo_Instance
import Definitions.Def_StochasticProg_ValueOfInfo_RP

namespace StochasticProg.ValueOfInfo

/-- Chapter 4, Proposition 7 (p. 173): `WS ≤ SPEV ≤ RP`, for a reference scenario
`ξ^r` whose probability `pᵣ = refProb I xir` is less than 1 (some other scenario is
possible). -/
theorem prop7_ws_le_spev_le_rp {n1 d K : ℕ} (I : Instance n1 d K)
    (xir : Fin d → ℝ) (hpr1 : refProb I xir < 1) :
    WS I ≤ SPEV I xir ∧ SPEV I xir ≤ RP I := by sorry

end StochasticProg.ValueOfInfo
