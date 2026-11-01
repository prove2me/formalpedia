-- Prove2me | Theorems.Thm_StatefulPricing_thm_3_4_proof_potential
-- name    : StatefulPricing.thm_3_4_proof_potential
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:26:28.366451+00:00
-- url     : https://prove2.me/theorems/c8b62d9e-4aeb-4243-adb2-63b9ccf1d5f2
-- title:
--   Proof of Theorem 3.4: in a Following round $\mathrm{Bad}_{t+1}\subseteq\mathrm{Bad}_t$ and $\phi(t+1)\le\phi(t)$
-- statement:
--   Consider a run of the chasing oracle of Theorem 3.4 with ties broken by an injective rank and a feasible target policy $\gamma$. If round $t\ge t_{\mathrm{init}}$ is Following, then, whichever price vector the oracle posts,
--   $$
--   \mathrm{Bad}_{t+1}\subseteq\mathrm{Bad}_t\qquad\text{and}\qquad \phi(t+1)\le\phi(t).
--   $$
--   Together with (I)–(III) of the proof of Theorem 3.6, this is what makes $\phi$ reach zero after $CW$ Missing rounds with the all-$1$ vector.
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

/-- **Following rounds do not raise the potential** (proof of Theorem 3.4, arXiv:2005.01869v2,
p.9): "notice that if t is a Following round, then Badt+1 ⊆ Badt, hence φ(t + 1) ≤ φ(t)."

For arbitrary valuations, ties broken by an injective rank and a feasible target policy, whichever
price vector the oracle posts: if round `t ≥ tinit` is `Following` then `Bad_{t+1} ⊆ Bad_t` and
`φ(t+1) ≤ φ(t)`. -/
theorem thm_3_4_proof_potential {T C W : ℕ} (c : Chase T C W) (hrank : Function.Injective c.rank)
    (hγ : IsFeasiblePolicy c.γ) (t : ℕ) (ht : c.tinit ≤ t) (hF : ¬ c.Missing t) :
    c.bad (t + 1) ⊆ c.bad t ∧ c.phi (t + 1) ≤ c.phi t := by sorry

end StatefulPricing
