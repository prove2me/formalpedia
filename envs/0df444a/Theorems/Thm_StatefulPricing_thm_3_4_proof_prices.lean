-- Prove2me | Theorems.Thm_StatefulPricing_thm_3_4_proof_prices
-- name    : StatefulPricing.thm_3_4_proof_prices
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:26:11.071548+00:00
-- url     : https://prove2.me/theorems/3b6ebafd-2082-4cd1-85b1-73a007a4283f
-- title:
--   Proof of Theorem 3.4: $\hat p_t$ is feasible, dominates $p^\gamma_t$, never sells Bad; late arrivals are Good
-- statement:
--   Consider a run of the chasing oracle of Theorem 3.4 on a DRACC instance, with a feasible target policy $\gamma$, start round $t_{\mathrm{init}}$, initial inventory $\hat\lambda_{t_{\mathrm{init}}}$ and any outcome of the coins. For every round $t\ge t_{\mathrm{init}}$:
--
--   1. the price vector $\hat p_t$ is feasible for $\hat\lambda_t$;
--   2. the oracle sells no resource of $\mathrm{Bad}_t$, whichever price vector it posts;
--   3. $\hat p_t(i)\ge p^\gamma_t(i)$ for every $i\in A_t$;
--   4. every resource $i$ with $t_a(i)=t>t_{\mathrm{init}}$ belongs to $\mathrm{Good}_t$.
--
--   These are the basic facts on which the potential argument for Theorems 3.4 and 3.6 rests.
--
--   Differences from the source:
--   - generalization: claim made in the proof of Theorem 3.4, for $k_t$-demand valuations → arbitrary valuations $v_t:2^{A_t}\to[0,1)$; reason: Theorem 3.6 reuses the claim for arbitrary valuations ("the same line of arguments", p.10); the claim does not use $k_t$-demand
--   - generalization: ties broken by the lexicographic order on $A_t$ → ties broken by an arbitrary injective rank on bundles; reason: every lexicographic order is induced by an injective rank, so the statement specializes to the source's
--   - encoding: random coins of the oracle, $\hat\lambda_{t_{\mathrm{init}}}$ an inventory vector on $A_{t_{\mathrm{init}}}$ → the coin outcomes are an arbitrary fixed sequence and $\hat\lambda_{t_{\mathrm{init}}}$ an arbitrary function $\mathbb N\to\mathbb N$; reason: the claim holds for every coin outcome; values off $A_{t_{\mathrm{init}}}$ are never read
--   - encoding: resources $[N]$, vectors indexed by $A_t$, prices in $(0,1]^{A_t}$ → resources are a finite set of natural numbers, inventory vectors $\mathbb N\to\mathbb N$ equal to $0$ off $A_t$, price vectors $\mathbb N\to\mathbb R$ with values in $(0,1]$ at every resource; reason: changes no demand set, payment or inventory
-- source:
--   Emek, Lavi, Niazadeh, Shi, Stateful Posted Pricing with Vanishing Regret via Dynamic Deterministic Markov Decision Processes, arXiv:2005.01869v2, proof of Theorem 3.4, p.9

import Mathlib
import Definitions.Def_StatefulPricing_Instance
import Definitions.Def_StatefulPricing_Chase

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace StatefulPricing

/-- **The oracle's prices** (proof of Theorem 3.4, arXiv:2005.01869v2, p.9): "observing that this
price vector is feasible for λ̂t by the definition of Goodt and Badt. Notice that OChasing never
sells a resource i ∈ Badt and that p̂t(i) ≥ p^γ_t(i) for all i ∈ At. Moreover, if resource i
arrives at time ta(i) = t > tinit, then i ∈ Goodt."

For every run of the oracle (any instance, rank, feasible target policy `γ`, start round, initial
inventory and coin outcomes) and every round `t ≥ tinit`:
1. `p̂_t` is feasible for `λ̂_t`;
2. the oracle sells no resource of `Bad_t` (whichever price vector it posts);
3. `p̂_t(i) ≥ p^γ_t(i)` for all `i ∈ A_t`;
4. a resource arriving at `ta(i) = t > tinit` is in `Good_t`. -/
theorem thm_3_4_proof_prices {T C W : ℕ} (c : Chase T C W) (hγ : IsFeasiblePolicy c.γ) :
    ∀ t, c.tinit ≤ t →
      Feasible (c.I.active t) (c.inv t) (c.hatPriceAt t) ∧
      Disjoint (c.I.demand c.rank t (c.priceAt t)) (c.bad t) ∧
      (∀ i ∈ c.I.active t, c.polPrice t i ≤ c.hatPriceAt t i) ∧
      (∀ i ∈ c.I.R, c.I.ta i = t → c.tinit < t → i ∈ c.good t) := by sorry

end StatefulPricing
