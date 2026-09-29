-- Prove2me | Theorems.Thm_StochasticProg_ValueOfInfo_prop8_rp_le_epev_le_evrs
-- name    : StochasticProg.ValueOfInfo.prop8_rp_le_epev_le_evrs
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T04:53:12.684654+00:00
-- url     : https://prove2.me/theorems/c9557014-5792-4436-beb9-6136b6d703f7
-- title:
--   Chapter 4, Proposition 8 — RP ≤ EPEV ≤ EVRS
-- statement:
--   This is Chapter 4, Proposition 8 (p. 174) of Birge & Louveaux, *Introduction to Stochastic
--   Programming*.
--
--   Let $I$ be a two-stage stochastic program with fixed recourse and finitely many scenarios
--   (an `Instance`). Fix a reference scenario $\xi^r$; let $p_r = \Pr(\xi=\xi^r)$ be its own
--   probability under $I$'s scenario distribution, and assume $p_r < 1$. For each scenario
--   $\xi^k$, let $\bar x^k$ be feasible ($\bar x^k \in K_1$) and optimal for the pairs subproblem
--   of $\xi^r,\xi^k$, i.e. $p_r\,z(\bar x^k,\xi^r)+(1-p_r)\,z(\bar x^k,\xi^k)$ (under the book's
--   $+\infty$-dominates convention) equals that subproblem's optimal value. Let $\bar x^r$ be
--   feasible and optimal for the single-scenario problem at $\xi^r$, i.e.
--   $z(\bar x^r,\xi^r) = \min_{x\in K_1} z(x,\xi^r)$.
--
--   The conclusion is the chain
--   $$
--   RP \le EPEV \le EVRS,
--   $$
--   where $RP$ is the recourse problem's optimal value, $EVRS = \mathbb E_\xi\,z(\bar x^r,\xi)$
--   is the expected cost of the reference-scenario solution $\bar x^r$, and $EPEV$ is the
--   smallest full expected cost $\mathbb E_\xi\,z(\bar x^k,\xi)$ among the $K+1$ candidate
--   solutions $\bar x^1,\dots,\bar x^K,\bar x^r$.
--
--   All three values are the optimal value of $\min_{x\in K_1}\mathbb E_\xi\,z(x,\xi)$ over
--   progressively smaller feasible sets: $RP$ over all of $K_1$, $EPEV$ over the $K+1$-point set
--   $\{\bar x^1,\dots,\bar x^K,\bar x^r\}\cap K_1$, and $EVRS$ over the single point $\bar x^r$
--   alone.
--
--   **Formalization Note** All quantities take values in the extended reals $\overline{\mathbb
--   R}$, combined by the book's own $+\infty$-dominates convention (p. 164), not Mathlib's
--   `EReal` arithmetic. The reference probability $p_r$ is not a free parameter but is computed
--   from $I$ and $\xi^r$ as `refProb I xir`; the hypothesis $p_r<1$ matches the pairs subproblem's
--   own weighting $p_r,1-p_r$.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, p. 174, Chapter 4, Proposition 8

import Mathlib
import Definitions.Def_StochasticProg_ValueOfInfo_Instance
import Definitions.Def_StochasticProg_ValueOfInfo_RP

namespace StochasticProg.ValueOfInfo

/-- Chapter 4, Proposition 8 (p. 174): `RP ≤ EPEV ≤ EVRS`, for a reference scenario
`ξ^r` whose probability `pᵣ = refProb I xir` is less than 1, `xBarK k` an optimal
solution to the pairs subproblem of `ξ^r,ξ^k` for each `k`, and `xBarR` an optimal
solution to `min_{x ∈ K1} z(x,ξ^r)`. -/
theorem prop8_rp_le_epev_le_evrs {n1 d K : ℕ} (I : Instance n1 d K)
    (xir : Fin d → ℝ) (hpr1 : refProb I xir < 1)
    (xBarK : Fin K → (Fin n1 → ℝ))
    (hxBarK_mem : ∀ k, xBarK k ∈ I.K1)
    (hxBarK_opt : ∀ k, badd ((refProb I xir : EReal) * I.z (xBarK k) xir)
        (((1 - refProb I xir : ℝ) : EReal) * I.z (xBarK k) (I.xi k)) =
        pairsValue I xir k)
    (xBarR : Fin n1 → ℝ) (hxBarR_mem : xBarR ∈ I.K1)
    (hxBarR_opt : I.z xBarR xir = ⨅ x ∈ I.K1, I.z x xir) :
    RP I ≤ EPEV I xBarK xBarR ∧ EPEV I xBarK xBarR ≤ EVRS I xBarR := by sorry

end StochasticProg.ValueOfInfo
