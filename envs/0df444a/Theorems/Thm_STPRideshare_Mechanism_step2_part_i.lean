-- Prove2me | Theorems.Thm_STPRideshare_Mechanism_step2_part_i
-- name    : STPRideshare.Mechanism.step2_part_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:33:20.483639+00:00
-- url     : https://prove2.me/theorems/c2609526-c90c-4e6b-bfcb-9a8c8d696c5f
-- title:
--   Proof of Theorem 2, Step 2, part (i), p. 54 — Φ^(t')_{a,t}(s_{t'}) ≥ Φ^(t)_{a,t}(s_t)
-- statement:
--   Fix an optimal selector and a valid economy, and consider the STP mechanism. Let $h_t$ be a reachable history with $t\le T-1$ and state $s_t$; let $t'\le t$ be the time at which the current plan was computed, so that nobody has deviated since $t'$, and let $s_{t'}$ be the state at $t'$. Let driver $i$ be available at $(a,t)$. Write $s_{t+1}$ for the state at $t+1$ if every driver follows the dispatch at $t$, and $\tilde s_{t+1}$ for the state at $t+1$ if every driver but $i$ follows the dispatch and $i$ relocates to $b$. Here $\Phi^{(t_1)}_{a,t_2}(s)=W(\mathcal D^{(t_1)}(s)\cup\{(1,a,t_2-t_1)\})-W(\mathcal D^{(t_1)}(s))$ is the replica gain (56) in the time-shifted economy $E^{(t_1)}(s)$.
--
--   Then
--   $$\Phi^{(t')}_{a,t}(s_{t'})\ \ge\ \Phi^{(t)}_{a,t}(s_t).$$
--
--   The replica gain at $(a,t)$ can only fall when the plan is recomputed at $t$ from the state the plan itself produced. With parts (ii) and (iii) it gives $\Phi^{(t')}_{a,t}(s_{t'})\ge\Phi^{(t+1)}_{b,t+\delta(a,b)}(\tilde s_{t+1})-c_{a,b,t}$: a relocation is not a useful deviation.
-- source:
--   Ma, Fang, Parkes, Spatio-Temporal Pricing for Ridesharing Platforms, arXiv:1801.04015v5, p. 54, proof of Theorem 2, Step 2, part (i)

import Mathlib
import Definitions.Def_STPRideshare_Mechanism_STP

namespace STPRideshare.Mechanism

/-- Proof of Theorem 2, Step 2, part (i), p. 54: with the current STP plan computed at time `t′`
in state `s_{t′}`, no deviation since, and driver `i` available at `(a, t)` in state `s_t`,
`Φ^{(t′)}_{a,t}(s_{t′}) ≥ Φ^{(t)}_{a,t}(s_t)`. -/
theorem step2_part_i {L : Type} [Fintype L] (sel : Selector L) (hsel : IsOptimalSelector sel)
    {ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ) (he : e.Valid)
    (h : Hist L ι κ) (hh : (stp sel).Reachable e h) (ht : h.length < e.P.T)
    (i : ι) (β : Bool) (a : L) (hs : stateAt e h i = .wait β a h.length) :
    PhiShift e h.length (stateAt e h) a h.length ≤
      PhiShift e (replanTime sel e h)
        (stateAt e (h.drop (h.length - replanTime sel e h))) a h.length := by sorry

end STPRideshare.Mechanism
