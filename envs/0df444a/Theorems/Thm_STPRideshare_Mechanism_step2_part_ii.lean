-- Prove2me | Theorems.Thm_STPRideshare_Mechanism_step2_part_ii
-- name    : STPRideshare.Mechanism.step2_part_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:33:23.579179+00:00
-- url     : https://prove2.me/theorems/505267ee-0241-4f29-b74d-e46c3d7ca02e
-- title:
--   Proof of Theorem 2, Step 2, part (ii), p. 54 — Φ^(t)_{a,t}(s_t) ≥ Φ^(t+1)_{b,t+δ(a,b)}(s_{t+1}) − c_{a,b,t}
-- statement:
--   Fix an optimal selector and a valid economy, and consider the STP mechanism. Let $h_t$ be a reachable history with $t\le T-1$ and state $s_t$; let $t'\le t$ be the time at which the current plan was computed, so that nobody has deviated since $t'$, and let $s_{t'}$ be the state at $t'$. Let driver $i$ be available at $(a,t)$. Write $s_{t+1}$ for the state at $t+1$ if every driver follows the dispatch at $t$, and $\tilde s_{t+1}$ for the state at $t+1$ if every driver but $i$ follows the dispatch and $i$ relocates to $b$. Here $\Phi^{(t_1)}_{a,t_2}(s)=W(\mathcal D^{(t_1)}(s)\cup\{(1,a,t_2-t_1)\})-W(\mathcal D^{(t_1)}(s))$ is the replica gain (56) in the time-shifted economy $E^{(t_1)}(s)$.
--
--   Then for every location $b$ with $t+\delta(a,b)\le T$,
--   $$\Phi^{(t)}_{a,t}(s_t)\ \ge\ \Phi^{(t+1)}_{b,t+\delta(a,b)}(s_{t+1})-c_{a,b,t}.$$
--
--   An additional driver at $(a,t)$ is worth at least as much as one at $(b,t+\delta(a,b))$ net of the cost of driving there. This is part (ii) of the three inequalities that show a relocation is not a useful deviation.
-- source:
--   Ma, Fang, Parkes, Spatio-Temporal Pricing for Ridesharing Platforms, arXiv:1801.04015v5, p. 54, proof of Theorem 2, Step 2, part (ii) (proof pp. 54–55)

import Mathlib
import Definitions.Def_STPRideshare_Mechanism_STP

namespace STPRideshare.Mechanism

/-- Proof of Theorem 2, Step 2, part (ii), p. 54: in the same setting, with `s_{t+1}` the state at
`t + 1` if every driver follows the dispatch at `t`,
`Φ^{(t)}_{a,t}(s_t) ≥ Φ^{(t+1)}_{b,t+δ(a,b)}(s_{t+1}) − c_{a,b,t}` for every `b` with
`t + δ(a, b) ≤ T`. -/
theorem step2_part_ii {L : Type} [Fintype L] (sel : Selector L) (hsel : IsOptimalSelector sel)
    {ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ) (he : e.Valid)
    (h : Hist L ι κ) (hh : (stp sel).Reachable e h) (ht : h.length < e.P.T)
    (i : ι) (β : Bool) (a : L) (hs : stateAt e h i = .wait β a h.length) :
    ∀ b : L, h.length + e.P.δ a b ≤ e.P.T →
      PhiShift e (h.length + 1) (stateAt e ((fun k => (stp sel).dispatch e h k) :: h)) b
          (h.length + e.P.δ a b) - e.P.c a b h.length ≤
        PhiShift e h.length (stateAt e h) a h.length := by sorry

end STPRideshare.Mechanism
