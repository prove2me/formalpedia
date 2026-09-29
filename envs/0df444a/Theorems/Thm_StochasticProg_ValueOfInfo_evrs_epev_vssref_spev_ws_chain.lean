-- Prove2me | Theorems.Thm_StochasticProg_ValueOfInfo_evrs_epev_vssref_spev_ws_chain
-- name    : StochasticProg.ValueOfInfo.evrs_epev_vssref_spev_ws_chain
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T04:53:49.272658+00:00
-- url     : https://prove2.me/theorems/5519e0ab-f6d7-4f24-8c21-7a9e16145530
-- title:
--   Chapter 4, Theorem 9 — EVRS/EPEV/VSS/SPEV/WS inequality chain
-- statement:
--   This is Chapter 4, Theorem 9 (p. 174) of Birge & Louveaux, *Introduction to Stochastic
--   Programming*, the chapter's capstone, obtained by combining Propositions 7 and 8 (and the
--   nonnegativity of Proposition 5).
--
--   Let $I$ be a two-stage stochastic program with fixed recourse and finitely many scenarios
--   (an `Instance`). Fix a reference scenario $\xi^r$; let $p_r = \Pr(\xi=\xi^r)$ be its own
--   probability under $I$'s scenario distribution, and assume $p_r < 1$. For each scenario
--   $\xi^k$, let $\bar x^k$ be feasible and optimal for the pairs subproblem of $\xi^r,\xi^k$
--   (i.e. $p_r\,z(\bar x^k,\xi^r)+(1-p_r)\,z(\bar x^k,\xi^k)$, under the book's $+\infty$-dominates
--   convention, attains that subproblem's optimal value). Let $\bar x^r$ be feasible and optimal
--   for the single-scenario problem at $\xi^r$.
--
--   The conclusion is the four-link chain
--   $$
--   0 \;\le\; EVRS - EPEV \;\le\; VSS \;\le\; EVRS - SPEV \;\le\; EVRS - WS,
--   $$
--   where $EVRS = \mathbb E_\xi\,z(\bar x^r,\xi)$, $VSS = EVRS - RP$ (the reference-scenario
--   generalization of the value of the stochastic solution), $EPEV$ is the smallest full
--   expected cost among the $K{+}1$ pairs-subproblem-optimal candidates
--   $\bar x^1,\dots,\bar x^K,\bar x^r$, $SPEV$ is the weighted average (over scenarios other than
--   $\xi^r$ itself) of the pairs-subproblem optimal values, and $WS$ is the wait-and-see value.
--   Every subtraction in the chain uses the book's own $+\infty$-dominates convention (p. 164).
--
--   Each of the five quantities $EVRS,EPEV,VSS,SPEV,WS$ is distinct and computed differently: the
--   chain gives two computable certified bounds ($EVRS-EPEV$ and $EVRS-SPEV$, each obtainable
--   from $K{+}1$ or $K$ cheap two-scenario linear programs) sandwiching $VSS$, which otherwise
--   requires solving the full $K$-scenario recourse problem $RP$ to compute exactly.
--
--   **Formalization Note** All quantities take values in the extended reals $\overline{\mathbb
--   R}$, and every addition/subtraction above (inside $EVRS-EPEV$, $VSS=EVRS-RP$, $EVRS-SPEV$,
--   $EVRS-WS$, and inside $SPEV$ and $EPEV$'s own definitions) uses the book's own convention that
--   $+\infty$ (infeasibility) dominates, i.e. $(+\infty)+(-\infty)=+\infty$ (p. 164), via the
--   `badd`/`bsub`/`bsum` operations — not Mathlib's `EReal` arithmetic, whose $\top+\bot=\bot$
--   would make the leftmost inequality $0\le EVRS-EPEV$ false whenever the reference-scenario
--   witness $\bar x^r$ is infeasible in a positive-probability scenario, exactly the book's own
--   Example 2 (pp. 174-175). The reference probability $p_r$ is not a free parameter but is
--   computed from $I$ and $\xi^r$ as `refProb I xir`. The nonnegativity of the leftmost gap
--   follows from Propositions 5(a) and 8 together with the identity $VSS = EVRS-RP$; the two
--   middle inequalities are Propositions 8 and 7 respectively, rearranged around
--   $VSS = EVRS - RP$.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, p. 174, Chapter 4, Theorem 9

import Mathlib
import Definitions.Def_StochasticProg_ValueOfInfo_Instance
import Definitions.Def_StochasticProg_ValueOfInfo_RP

namespace StochasticProg.ValueOfInfo

/-- Chapter 4, Theorem 9 (p. 174), the chapter's capstone:
`0 ≤ EVRS − EPEV ≤ VSS ≤ EVRS − SPEV ≤ EVRS − WS`, for a reference scenario `ξ^r`
whose probability `pᵣ = refProb I xir` is less than 1, `xBarK k` an optimal
solution to the pairs subproblem of `ξ^r,ξ^k` for each `k`, and `xBarR` an optimal
solution to `min_{x ∈ K1} z(x,ξ^r)`. All differences use the book's `+∞`
convention (p. 164). -/
theorem evrs_epev_vssref_spev_ws_chain {n1 d K : ℕ} (I : Instance n1 d K)
    (xir : Fin d → ℝ) (hpr1 : refProb I xir < 1)
    (xBarK : Fin K → (Fin n1 → ℝ))
    (hxBarK_mem : ∀ k, xBarK k ∈ I.K1)
    (hxBarK_opt : ∀ k, badd ((refProb I xir : EReal) * I.z (xBarK k) xir)
        (((1 - refProb I xir : ℝ) : EReal) * I.z (xBarK k) (I.xi k)) =
        pairsValue I xir k)
    (xBarR : Fin n1 → ℝ) (hxBarR_mem : xBarR ∈ I.K1)
    (hxBarR_opt : I.z xBarR xir = ⨅ x ∈ I.K1, I.z x xir) :
    (0 : EReal) ≤ bsub (EVRS I xBarR) (EPEV I xBarK xBarR) ∧
      bsub (EVRS I xBarR) (EPEV I xBarK xBarR) ≤ VSSRef I xBarR ∧
      VSSRef I xBarR ≤ bsub (EVRS I xBarR) (SPEV I xir) ∧
      bsub (EVRS I xBarR) (SPEV I xir) ≤ bsub (EVRS I xBarR) (WS I) := by sorry

end StochasticProg.ValueOfInfo
