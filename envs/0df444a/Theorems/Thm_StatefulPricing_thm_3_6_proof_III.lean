-- Prove2me | Theorems.Thm_StatefulPricing_thm_3_6_proof_III
-- name    : StatefulPricing.thm_3_6_proof_III
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T08:26:11.313991+00:00
-- url     : https://prove2.me/theorems/48e4ae6c-9c82-4534-b17f-2438d1df36bc
-- title:
--   Proof of Theorem 3.6, (III): once $\phi$ is zero it stays zero
-- statement:
--   Consider a run of the chasing oracle of Theorem 3.4 on a DRACC instance with arbitrary valuations, ties broken by an injective rank, a feasible target policy, any initial inventory and any outcome of the coins. If $\phi(t)=0$ for some $t_{\mathrm{init}}\le t\le t_{\mathrm{final}}$, then
--   $$
--   \phi(t')=0\qquad\text{for all } t<t'\le t_{\mathrm{final}}.
--   $$
--   Since $\phi(t)=0$ means $\mathrm{Bad}_t=\emptyset$, there are no Missing rounds after that point.
--
--   Differences from the source:
--   - generalization: ties broken by the lexicographic order on $A_t$ → ties broken by an arbitrary injective rank on bundles; reason: every lexicographic order is induced by an injective rank, so the statement specializes to the source's
--   - encoding: random coins of the oracle, $\hat\lambda_{t_{\mathrm{init}}}$ an inventory vector on $A_{t_{\mathrm{init}}}$ → the coin outcomes are an arbitrary fixed sequence and $\hat\lambda_{t_{\mathrm{init}}}$ an arbitrary function $\mathbb N\to\mathbb N$; reason: the claim holds for every coin outcome; values off $A_{t_{\mathrm{init}}}$ are never read
--   - encoding: resources $[N]$, vectors indexed by $A_t$, prices in $(0,1]^{A_t}$ → resources are a finite set of natural numbers, inventory vectors $\mathbb N\to\mathbb N$ equal to $0$ off $A_t$, price vectors $\mathbb N\to\mathbb R$ with values in $(0,1]$ at every resource; reason: changes no demand set, payment or inventory
-- source:
--   Emek, Lavi, Niazadeh, Shi, Stateful Posted Pricing with Vanishing Regret via Dynamic Deterministic Markov Decision Processes, arXiv:2005.01869v2, proof of Theorem 3.6, (III), p.10

import Mathlib
import Definitions.Def_StatefulPricing_Instance
import Definitions.Def_StatefulPricing_Chase

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace StatefulPricing

/-- **(III) of the proof of Theorem 3.6** (arXiv:2005.01869v2, p.10): "(III) if φ(t) = 0 for some
tinit ≤ t ≤ tfinal, then φ(t′) = 0 for all t < t′ ≤ tfinal."

For arbitrary valuations, ties broken by an injective rank, a feasible target policy, any initial
inventory and coin outcomes. -/
theorem thm_3_6_proof_III {T C W : ℕ} (c : Chase T C W) (hrank : Function.Injective c.rank)
    (hγ : IsFeasiblePolicy c.γ) (tfinal : ℕ) :
    ∀ t, c.tinit ≤ t → t ≤ tfinal → c.phi t = 0 →
      ∀ t', t < t' → t' ≤ tfinal → c.phi t' = 0 := by sorry

end StatefulPricing
