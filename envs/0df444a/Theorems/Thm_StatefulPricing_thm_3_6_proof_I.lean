-- Prove2me | Theorems.Thm_StatefulPricing_thm_3_6_proof_I
-- name    : StatefulPricing.thm_3_6_proof_I
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T08:26:03.31586+00:00
-- url     : https://prove2.me/theorems/69aae2db-fa9f-4951-a609-af55b31efc43
-- title:
--   Proof of Theorem 3.6, (I): $0\le\phi(t)\le CW$
-- statement:
--   Consider a run of the chasing oracle of Theorem 3.4 on a DRACC instance with capacities at most $C$ and at most $W$ simultaneously active resources, with arbitrary valuations, any target policy, any initial inventory and any outcome of the coins. Then for every $t_{\mathrm{init}}\le t\le t_{\mathrm{final}}$,
--   $$
--   0\le\phi(t)\le CW.
--   $$
--   This caps the number of consecutive Missing rounds with the all-$1$ vector before $\phi$ reaches zero.
--
--   Differences from the source:
--   - generalization: target policy $\gamma\in\Gamma$, a feasible pricing policy → any pricing policy $\gamma$; reason: feasibility of $\gamma$ is not used; the statement specializes to feasible $\gamma$
--   - encoding: random coins of the oracle, $\hat\lambda_{t_{\mathrm{init}}}$ an inventory vector on $A_{t_{\mathrm{init}}}$ → the coin outcomes are an arbitrary fixed sequence and $\hat\lambda_{t_{\mathrm{init}}}$ an arbitrary function $\mathbb N\to\mathbb N$; reason: the claim holds for every coin outcome; values off $A_{t_{\mathrm{init}}}$ are never read
--   - encoding: resources $[N]$, vectors indexed by $A_t$, prices in $(0,1]^{A_t}$ → resources are a finite set of natural numbers, inventory vectors $\mathbb N\to\mathbb N$ equal to $0$ off $A_t$, price vectors $\mathbb N\to\mathbb R$ with values in $(0,1]$ at every resource; reason: changes no demand set, payment or inventory
-- source:
--   Emek, Lavi, Niazadeh, Shi, Stateful Posted Pricing with Vanishing Regret via Dynamic Deterministic Markov Decision Processes, arXiv:2005.01869v2, proof of Theorem 3.6, (I), p.10

import Mathlib
import Definitions.Def_StatefulPricing_Instance
import Definitions.Def_StatefulPricing_Chase

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace StatefulPricing

/-- **(I) of the proof of Theorem 3.6** (arXiv:2005.01869v2, p.10): "(I) 0 ≤ φ(t) ≤ CW for every
tinit ≤ t ≤ tfinal".

For every run of the oracle (arbitrary valuations, any target policy, initial inventory and coin
outcomes) and every `tinit ≤ t ≤ tfinal`, `0 ≤ φ(t) ≤ C·W`. -/
theorem thm_3_6_proof_I {T C W : ℕ} (c : Chase T C W) (tfinal : ℕ) :
    ∀ t, c.tinit ≤ t → t ≤ tfinal → 0 ≤ c.phi t ∧ c.phi t ≤ (C * W : ℤ) := by sorry

end StatefulPricing
