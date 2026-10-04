-- Prove2me | Theorems.Thm_SennottDP_FiniteHorizon_approx_stationary_limit_point
-- name    : SennottDP.FiniteHorizon.approx_stationary_limit_point
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T06:36:12.799644+00:00
-- url     : https://prove2.me/theorems/b2a58177-b6a8-4615-905b-faa5ed5f30ff
-- title:
--   Proposition B.5 — every sequence of stationary policies for an approximating sequence has a limit point
-- statement:
--   Let $(\Delta_N)$ be an approximating sequence for the MDC $\Delta$ with countable state space $S$, and let $e^N$ be a stationary policy for $\Delta_N$ ($e^N(i) \in A_i$ for $i \in S_N$), $N \ge N_0$. Then $(e^N)$ has a limit point: a stationary policy $e$ for $\Delta$ and a subsequence $(N_r)$ with
--   $$
--   e^{N_r}(i) = e(i) \quad \text{for } N_r \text{ sufficiently large}, \qquad i \in S.
--   $$
--
--   Here, unlike in Proposition B.3, each $e^N$ is defined only on the finite set $S_N$. This result provides the candidate optimal policy for $\Delta$ in Theorem 3.2.3.
--
--   **Formalization Note** A stationary policy for $\Delta_N$ is a function on $S$ whose values on $S_N$ are admissible; its values off $S_N$ are irrelevant, since for each $i$ they enter only finitely many terms.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 290, Proposition B.5 (Definition B.4)

import Mathlib
import Definitions.Def_SennottDP_FiniteHorizon_MDC
import Definitions.Def_SennottDP_FiniteHorizon_Criterion
import Definitions.Def_SennottDP_FiniteHorizon_ApproxSeq

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.FiniteHorizon

/-- Proposition B.5 (Sennott, p. 290). Let `(Δ_N)` be an approximating sequence for `Δ`. Every
sequence `(e^N)` of stationary policies for `(Δ_N)` has a limit point (Definition B.4): a
stationary policy `e` for `Δ` and a subsequence `N_r` with `e^{N_r}(i) = e(i)` for `N_r`
sufficiently large, for each `i ∈ S`. -/
theorem approx_stationary_limit_point {S Act : Type} [Countable S] (M : MDC S Act)
    (AS : M.ApproxSeq) (e : ℕ → S → Act) (he : AS.IsStationarySeq e) :
    ∃ f : M.Stationary, M.IsApproxLimitPoint e f := by sorry

end SennottDP.FiniteHorizon
