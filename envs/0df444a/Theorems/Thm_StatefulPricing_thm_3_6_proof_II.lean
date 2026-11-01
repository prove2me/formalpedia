-- Prove2me | Theorems.Thm_StatefulPricing_thm_3_6_proof_II
-- name    : StatefulPricing.thm_3_6_proof_II
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:26:18.783825+00:00
-- url     : https://prove2.me/theorems/5237ee14-4b77-44e3-ae1e-f5df7b60d5e9
-- title:
--   Proof of Theorem 3.6, (II): a Missing round with the all-1 vector strictly lowers $\phi$
-- statement:
--   Consider a run of the chasing oracle of Theorem 3.4 on a DRACC instance with arbitrary valuations, any target policy, any initial inventory and any outcome of the coins. If $t_{\mathrm{init}}\le t<t_{\mathrm{final}}$ is a Missing round and the oracle posts the all-$1$ price vector in round $t$, then
--   $$
--   \phi(t+1)<\phi(t).
--   $$
--
--   Differences from the source:
--   - generalization: target policy $\gamma\in\Gamma$, a feasible pricing policy → any pricing policy $\gamma$; reason: feasibility of $\gamma$ is not used; the statement specializes to feasible $\gamma$
--   - encoding: random coins of the oracle, $\hat\lambda_{t_{\mathrm{init}}}$ an inventory vector on $A_{t_{\mathrm{init}}}$ → the coin outcomes are an arbitrary fixed sequence and $\hat\lambda_{t_{\mathrm{init}}}$ an arbitrary function $\mathbb N\to\mathbb N$; reason: the claim holds for every coin outcome; values off $A_{t_{\mathrm{init}}}$ are never read
--   - encoding: resources $[N]$, vectors indexed by $A_t$, prices in $(0,1]^{A_t}$ → resources are a finite set of natural numbers, inventory vectors $\mathbb N\to\mathbb N$ equal to $0$ off $A_t$, price vectors $\mathbb N\to\mathbb R$ with values in $(0,1]$ at every resource; reason: changes no demand set, payment or inventory
-- source:
--   Emek, Lavi, Niazadeh, Shi, Stateful Posted Pricing with Vanishing Regret via Dynamic Deterministic Markov Decision Processes, arXiv:2005.01869v2, proof of Theorem 3.6, (II), p.10

import Mathlib
import Definitions.Def_StatefulPricing_Instance
import Definitions.Def_StatefulPricing_Chase

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace StatefulPricing

/-- **(II) of the proof of Theorem 3.6** (arXiv:2005.01869v2, p.10): "(II) if tinit ≤ t < tfinal
is a Missing round and OChasing posts the all-1 price vector in round t, then φ(t + 1) < φ(t)".

For every run of the oracle (arbitrary valuations, any target policy, initial inventory and coin
outcomes): if `tinit ≤ t < tfinal`, round `t` is `Missing` and the oracle posts the all-1 vector at
`t`, then `φ(t+1) < φ(t)`. -/
theorem thm_3_6_proof_II {T C W : ℕ} (c : Chase T C W) (tfinal : ℕ) :
    ∀ t, c.tinit ≤ t → t < tfinal → c.Missing t → c.coin t = true →
      c.phi (t + 1) < c.phi t := by sorry

end StatefulPricing
