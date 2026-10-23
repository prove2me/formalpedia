-- Prove2me | Theorems.Thm_STPRideshare_Mechanism_step2_part_iii
-- name    : STPRideshare.Mechanism.step2_part_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:33:28.465978+00:00
-- url     : https://prove2.me/theorems/c4d66fd8-f81c-49a7-b841-323e6eedc414
-- title:
--   Proof of Theorem 2, Step 2, part (iii), p. 54 — Φ^(t+1)_{b,t+δ(a,b)}(s_{t+1}) ≥ Φ^(t+1)_{b,t+δ(a,b)}(s̃_{t+1})
-- statement:
--   Fix an optimal selector and a valid economy, and consider the STP mechanism. Let $h_t$ be a reachable history with $t\le T-1$ and state $s_t$; let $t'\le t$ be the time at which the current plan was computed, so that nobody has deviated since $t'$, and let $s_{t'}$ be the state at $t'$. Let driver $i$ be available at $(a,t)$. Write $s_{t+1}$ for the state at $t+1$ if every driver follows the dispatch at $t$, and $\tilde s_{t+1}$ for the state at $t+1$ if every driver but $i$ follows the dispatch and $i$ relocates to $b$. Here $\Phi^{(t_1)}_{a,t_2}(s)=W(\mathcal D^{(t_1)}(s)\cup\{(1,a,t_2-t_1)\})-W(\mathcal D^{(t_1)}(s))$ is the replica gain (56) in the time-shifted economy $E^{(t_1)}(s)$.
--
--   Then for every location $b$ with $t+\delta(a,b)\le T$,
--   $$\Phi^{(t+1)}_{b,t+\delta(a,b)}(s_{t+1})\ \ge\ \Phi^{(t+1)}_{b,t+\delta(a,b)}(\tilde s_{t+1}).$$
--
--   Moving driver $i$ herself to $(b,t+\delta(a,b))$ lowers the marginal value of another driver there at least as much as leaving her on her dispatched path: drivers at the same node are stronger substitutes than drivers at different nodes.
--
--   **Formalization Note.** In the game, $\tilde s_{t+1}$ is the state with driver $i$ en route on $(a,b,t)$ (or available at $(b,t+1)$ if $\delta(a,b)=1$); its type in $E^{(t+1)}$ is $(1,b,t+\delta(a,b)-(t+1))$, the same as the page's $(1,b,t+\delta(a,b))$.
-- source:
--   Ma, Fang, Parkes, Spatio-Temporal Pricing for Ridesharing Platforms, arXiv:1801.04015v5, p. 54, proof of Theorem 2, Step 2, part (iii) (proof pp. 55–56)

import Mathlib
import Definitions.Def_STPRideshare_Mechanism_STP

namespace STPRideshare.Mechanism

open scoped Classical in
/-- Proof of Theorem 2, Step 2, part (iii), p. 54: in the same setting, with `s_{t+1}` the state at
`t + 1` if every driver follows the dispatch at `t` and `s̃_{t+1}` the state if only driver `i`
deviates and relocates to `b`,
`Φ^{(t+1)}_{b,t+δ(a,b)}(s_{t+1}) ≥ Φ^{(t+1)}_{b,t+δ(a,b)}(s̃_{t+1})` for every `b` with
`t + δ(a, b) ≤ T`. -/
theorem step2_part_iii {L : Type} [Fintype L] (sel : Selector L) (hsel : IsOptimalSelector sel)
    {ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ) (he : e.Valid)
    (h : Hist L ι κ) (hh : (stp sel).Reachable e h) (ht : h.length < e.P.T)
    (i : ι) (β : Bool) (a : L) (hs : stateAt e h i = .wait β a h.length) :
    ∀ b : L, h.length + e.P.δ a b ≤ e.P.T →
      PhiShift e (h.length + 1)
          (stateAt e (Function.update (fun k => (stp sel).dispatch e h k) i (.move b) :: h)) b
          (h.length + e.P.δ a b) ≤
        PhiShift e (h.length + 1) (stateAt e ((fun k => (stp sel).dispatch e h k) :: h)) b
          (h.length + e.P.δ a b) := by sorry

end STPRideshare.Mechanism
