-- Prove2me | Theorems.Thm_StatefulPricing_theorem_3_10
-- name    : StatefulPricing.theorem_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:26:15.528986+00:00
-- url     : https://prove2.me/theorems/14fd516d-d2d9-4dfa-871d-5bfc0e6da6a2
-- title:
--   Theorem 3.10: some posted price mechanism has regret $O(T^{\frac12(1+\frac{CW}{CW+1})}\sqrt{\log|\Gamma|})$ on every DRACC instance
-- statement:
--   There is an absolute constant $K$ with the following property. For all $C,W,T$, every injective tie-breaking order and every finite nonempty family $\Gamma$ of feasible pricing policies, there is a randomized posted price mechanism which posts feasible prices at every round, uses only the information revealed before each round, and satisfies, on every DRACC instance with horizon $T$, capacities at most $C$, at most $W$ simultaneously active resources and arbitrary valuations $v_t:2^{A_t}\to[0,1)$,
--   $$
--   \max_{\gamma\in\Gamma}\sum_{t=1}^T\hat q^{\gamma}_t-\mathbb E\Big[\sum_{t=1}^T\hat q^{p_t}_t\Big]\le K\,T^{\frac12\left(1+\frac{CW}{CW+1}\right)}\sqrt{\log|\Gamma|}.
--   $$
--   The mechanism is the paper's LBPP: C&S run on the induced Dd-MDP with the chasing oracle of Theorem 3.6 and an OLSC algorithm from Theorem 3.7. The bound is sublinear in $T$ for fixed $C$ and $W$, so the stateful benchmark of the best pricing policy in hindsight is approached at a vanishing rate per round.
--
--   Differences from the source:
--   - reading: "the regret of LBPP is $O(\cdot)$" → there exists a non-anticipating, always feasible randomized mechanism with regret at most $K\cdot T^{\frac12(1+\frac{CW}{CW+1})}\sqrt{\log|\Gamma|}$ on every instance; reason: LBPP is C&S with an OLSC algorithm the paper does not pin down; LBPP is the witness
--   - reading: "an adaptive adversary simultaneously picks the valuation function $v_t$" (p.5) → the instance is fixed before the mechanism's coins (oblivious adversary); reason: the regret puts the benchmark outside an expectation "taken over the decision maker's randomness" (p.6), which is well defined only for a fixed instance
--   - reading: $O(\cdot)$ → one absolute constant $K$, chosen before $C$, $W$, $T$, the rank and $\Gamma$; reason: the stronger reading; it holds by the proof (constant $2.66$ in Theorem 3.6, Theorem 3.8's depends only on Theorem 3.7's), and Theorem 3.9 prints its $C,W$ dependence
--   - generalization: ties broken by the lexicographic order on $A_t$ → ties broken by an arbitrary injective rank on bundles; reason: every lexicographic order is induced by an injective rank, so the statement specializes to the source's
--   - encoding: resources $[N]$, vectors indexed by $A_t$, prices in $(0,1]^{A_t}$, policies on $\{0,\dots,C\}^{A_t}$, $\log$, a set $\Gamma$ → resources a finite set of natural numbers, inventory vectors $\mathbb N\to\mathbb N$ equal to $0$ off $A_t$, price vectors $\mathbb N\to\mathbb R$ with values in $(0,1]$ everywhere, policies taking $(A_t,\lambda)$, natural logarithm, $\Gamma$ a family indexed by a finite nonempty type; reason: changes no instance: prices off $A_t$ are never read, a policy on $A_t$ extends by $1$, the base of $\log$ changes only $K$, and a set $\Gamma$ is the family indexed by itself
-- source:
--   Emek, Lavi, Niazadeh, Shi, Stateful Posted Pricing with Vanishing Regret via Dynamic Deterministic Markov Decision Processes, arXiv:2005.01869v2, Theorem 3.10, p.12

import Mathlib
import Definitions.Def_StatefulPricing_Instance
import Definitions.Def_StatefulPricing_Mechanism

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace StatefulPricing

/-- **Theorem 3.10** (arXiv:2005.01869v2, p.12): "The regret of LBPP for T-round DRACC instances with
with arbitrary valuation functions is O(T^{1/2(1+CW/(CW+1))} √log |Γ|)."

There is an absolute constant `K` such that for all `C`, `W`, `T`, every injective tie-breaking
rank and every finite nonempty family `Γ` of feasible pricing policies, some randomized posted
price mechanism, non-anticipating and always feasible, has regret at most
`K · T^{½(1 + CW/(CW+1))} · √(log |Γ|)` on every DRACC instance with horizon `T`, capacities at most
`C` and at most `W` simultaneously active resources, with arbitrary valuations in `[0,1)`.

**Formalization Note.** "The regret of LBPP is O(·)" is stated as the existence of a mechanism
(LBPP is the witness; the paper does not pin its OLSC subroutine). The mechanism is chosen after
`T`, `C`, `W`, the rank and `Γ` and before the instance; the instance is fixed (oblivious
adversary) and the expectation is over the mechanism's coins. `log` is the natural logarithm. -/
theorem theorem_3_10 :
    ∃ K : ℝ, ∀ (C W T : ℕ) (rank : Finset ℕ → ℕ), Function.Injective rank →
      ∀ (ι : Type) [Fintype ι] [Nonempty ι] (Γ : ι → Policy), (∀ j, IsFeasiblePolicy (Γ j)) →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
        ∃ M : Mechanism Ω T C W, M.NonAnticipating ∧ M.AlwaysFeasible rank ∧
          ∀ I : Instance T C W, M.regret rank P I Γ
            ≤ K * (T : ℝ) ^ ((1 / 2 : ℝ) * (1 + (C * W : ℝ) / (C * W + 1)))
                * Real.sqrt (Real.log (Fintype.card ι)) := by sorry

end StatefulPricing
