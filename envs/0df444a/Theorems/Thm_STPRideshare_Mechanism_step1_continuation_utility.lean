-- Prove2me | Theorems.Thm_STPRideshare_Mechanism_step1_continuation_utility
-- name    : STPRideshare.Mechanism.step1_continuation_utility
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:33:23.841898+00:00
-- url     : https://prove2.me/theorems/e6330363-999d-4152-b9e3-056c1b99539d
-- title:
--   Proof of Theorem 2, Step 2, p. 54 (from Step 1) — under σ*, an available driver's continuation utility is Φ^(t')_{a,t}(s_{t'}), or its positive part if she has not entered
-- statement:
--   Fix an optimal selector and a valid economy, and consider the STP mechanism. Let $h_t$ be a reachable history with $t\le T-1$; let $t'\le t$ be the time at which the current plan was computed (time $0$, or the last time following a deviation), so that no driver has deviated since $t'$, and let $s_{t'}$ be the state at $t'$. If driver $i$ is available at $(a,t)$, then her continuation utility $\sum_{t''=t}^{T-1}\hat\pi_{i,t''}$ when every driver follows the dispatches from $h_t$ on is
--   $$\Phi^{(t')}_{a,t}(s_{t'})\ \text{ if } s_{i,t}=(1,a,t),\qquad \max\{\Phi^{(t')}_{a,t}(s_{t'}),0\}\ \text{ if } s_{i,t}=(0,a,t),$$
--   where $\Phi^{(t')}_{a,t}(s_{t'})=W(\mathcal D^{(t')}(s_{t'})\cup\{(1,a,t-t')\})-W(\mathcal D^{(t')}(s_{t'}))$.
--
--   This identifies the value of following the plan, against which Step 2 compares every deviation.
-- source:
--   Ma, Fang, Parkes, Spatio-Temporal Pricing for Ridesharing Platforms, arXiv:1801.04015v5, p. 54, proof of Theorem 2, Step 2 (consequence of Step 1, p. 53); (56) p. 53

import Mathlib
import Definitions.Def_STPRideshare_Mechanism_STP

namespace STPRideshare.Mechanism

/-- Proof of Theorem 2, Step 1 as used in Step 2, p. 54: if the current STP plan was computed at
time `t′` in state `s_{t′}` and nobody has deviated since, then under `σ*` a driver available at
`(a, t)` gets continuation utility `Φ^{(t′)}_{a,t}(s_{t′})` if she has entered (`β = 1`) and
`max{Φ^{(t′)}_{a,t}(s_{t′}), 0}` if she has not (`β = 0`). -/
theorem step1_continuation_utility {L : Type} [Fintype L] (sel : Selector L) (hsel : IsOptimalSelector sel)
    {ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ) (he : e.Valid)
    (h : Hist L ι κ) (hh : (stp sel).Reachable e h) (ht : h.length < e.P.T)
    (i : ι) (β : Bool) (a : L) (hs : stateAt e h i = .wait β a h.length) :
    (stp sel).contUtil e ((stp sel).sigmaStar e) h i =
      if β = true then
        PhiShift e (replanTime sel e h)
          (stateAt e (h.drop (h.length - replanTime sel e h))) a h.length
      else
        max (PhiShift e (replanTime sel e h)
          (stateAt e (h.drop (h.length - replanTime sel e h))) a h.length) 0 := by sorry

end STPRideshare.Mechanism
