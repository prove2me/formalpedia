-- Prove2me | Theorems.Thm_StatefulPricing_thm_3_4_proof_following
-- name    : StatefulPricing.thm_3_4_proof_following
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:26:19.60696+00:00
-- url     : https://prove2.me/theorems/222794da-23d7-45d9-b388-3d43bf6b730f
-- title:
--   Proof of Theorem 3.4: in a Following round the oracle sells what $\gamma$ sells, or nothing
-- statement:
--   Consider a run of the chasing oracle of Theorem 3.4 with ties broken by an injective rank and a feasible target policy $\gamma$, and let $t\ge t_{\mathrm{init}}$ be a Following round (no resource of $\mathrm{Bad}_t$ is sold by $\gamma$). Then:
--
--   1. if the oracle posts $\hat p_t$, its demand set equals $\gamma$'s demand set $\hat A^{p^\gamma_t}_t$, and $\hat p_t(i)=p^\gamma_t(i)$ for every $i$ in it, so it sells exactly the same resources at the same prices;
--   2. if the oracle posts the all-$1$ price vector, its demand set is empty.
--
--   This bounds the oracle's expected loss in Following rounds by $\varepsilon$ per round.
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

/-- **Following rounds copy `γ`** (proof of Theorem 3.4, arXiv:2005.01869v2, p.9): "For each
Following round t, if OChasing posts p̂t in round t, then OChasing sells exactly the same resources
as γ for the exact same prices; otherwise (OChasing posts the all-1 price vector in round t),
OChasing does not sell any resource."

For arbitrary valuations, ties broken by an injective rank and a feasible target policy: in a
`Following` round `t ≥ tinit`, if the oracle posts `p̂_t` its demand set equals `γ`'s and the prices
agree on it; if it posts the all-1 vector its demand set is empty. -/
theorem thm_3_4_proof_following {T C W : ℕ} (c : Chase T C W) (hrank : Function.Injective c.rank)
    (hγ : IsFeasiblePolicy c.γ) (t : ℕ) (ht : c.tinit ≤ t) (hF : ¬ c.Missing t) :
    (c.coin t = false →
      c.I.demand c.rank t (c.priceAt t) = c.I.demand c.rank t (c.polPrice t) ∧
      ∀ i ∈ c.I.demand c.rank t (c.polPrice t), c.priceAt t i = c.polPrice t i) ∧
    (c.coin t = true → c.I.demand c.rank t (c.priceAt t) = ∅) := by sorry

end StatefulPricing
