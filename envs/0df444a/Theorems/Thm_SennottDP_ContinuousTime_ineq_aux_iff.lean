-- Prove2me | Theorems.Thm_SennottDP_ContinuousTime_ineq_aux_iff
-- name    : SennottDP.ContinuousTime.ineq_aux_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T11:11:47.171895+00:00
-- url     : https://prove2.me/theorems/b7dc0710-090a-44ad-916c-5cdaa01e25f9
-- title:
--   Lemma 10.3.2 — inequality (10.15) for Ψ and inequality (10.20) for the auxiliary MDC Δ are equivalent
-- statement:
--   Let $\Psi$ be a CTMDC satisfying Assumption (CTB) with the constant $\tau$, let $\Delta$ be the auxiliary MDC built with $\tau$, let $e$ be a stationary policy and $Z$ a finite constant.
--
--   1. If $w$ is a real function on $S$ such that, for every $i$, $\sum_j P^*_{ij}(e)w(j)$ converges and
--   $$Z+w(i)\ge C(i,e)+\sum_j P^*_{ij}(e)w(j),$$
--   then $Z$ and $z=\tau w$ satisfy (10.15): for every $i$, $\sum_j P_{ij}(e)z(j)$ converges and $Z\tau(i,e)+z(i)\ge G(i,e)+g(i,e)\tau(i,e)+\sum_j P_{ij}(e)z(j)$.
--   2. Conversely, if $Z$ and a real function $z$ satisfy (10.15), then $Z$ and $w=z/\tau$ satisfy (10.20).
--
--   The lemma transfers average cost inequalities between the continuous time chain and its discrete time auxiliary chain; it is the step that lets an optimal policy computed for $\Delta$ be certified for $\Psi$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 246, Lemma 10.3.2, eqs. (10.15), (10.19), (10.20)

import Mathlib
import Definitions.Def_SennottDP_ContinuousTime_CTMDC

namespace SennottDP.ContinuousTime

/-- Lemma 10.3.2 (p. 246). -/
theorem ineq_aux_iff {S Act : Type} [Countable S] (Ψ : CTMDC S Act) (hΨ : Ψ.IsValid)
    (tau B : ℝ) (hCTB : Ψ.CTB tau B) (e : S → Act) (he : ∀ i, e i ∈ Ψ.A i) (Z : ℝ) :
    (∀ w : S → ℝ, Ψ.Ineq1020 tau e Z w → Ψ.Ineq1015 e Z (fun i => tau * w i)) ∧
      (∀ z : S → ℝ, Ψ.Ineq1015 e Z z → Ψ.Ineq1020 tau e Z (fun i => z i / tau)) := by sorry

end SennottDP.ContinuousTime
