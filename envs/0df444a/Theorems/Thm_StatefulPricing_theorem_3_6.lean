-- Prove2me | Theorems.Thm_StatefulPricing_theorem_3_6
-- name    : StatefulPricing.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:26:25.665075+00:00
-- url     : https://prove2.me/theorems/05720dc3-b30a-450e-9796-50a053a1242d
-- title:
--   Theorem 3.6: DRACC Dd-MDPs with arbitrary valuations are $O(T^{CW/(CW+1)})$-chasable
-- statement:
--   There is an absolute constant $K_0$ with the following property. For all $C,W,T$ and every injective tie-breaking rank there is a single randomized online chasing oracle $\mathcal O$, fixed before the instance, such that on the Dd-MDP of every DRACC instance with horizon $T$, capacities at most $C$, at most $W$ simultaneously active resources and arbitrary valuations, for every feasible pricing policy $\gamma$, every $1\le t_{\mathrm{init}}\le t_{\mathrm{final}}\le T$ and every initial state, the oracle plays feasible actions and its chasing regret satisfies
--   $$
--   \mathrm{CR}\le K_0\,T^{\frac{CW}{CW+1}}.
--   $$
--   This is the chasability input of the reduction: with Theorem 3.8 it gives the goal theorem.
--
--   Differences from the source:
--   - reading: $O(T^{CW/(CW+1)})$-chasable → one absolute constant $K_0$, chosen before $C$, $W$, $T$; reason: the proof gives $\mathrm{CR}\le\varepsilon T+CW/\varepsilon^{CW}\le 2.66\,T^{CW/(CW+1)}$ (and $\mathrm{CR}\le T$ when $T\le CW$); Theorem 3.9 prints its $C,W$ dependence, so the paper's $O$-constants are absolute
--   - reading: "admits an ongoing chasing oracle" → one online oracle chosen after $C,W,T$ and the rank and before the instance, seeing $s_1$ and $g_s,f_s$ for $s<t$; reason: an oracle chosen after the instance could read the future; the Theorem 3.4 oracle runs $\gamma$ from round 1 (p.9)
--   - generalization: the initial inventory vector $\hat\lambda_{t_{\mathrm{init}}}$ (an inventory vector on $A_{t_{\mathrm{init}}}$) → an arbitrary state $(A,\lambda)$ of the induced Dd-MDP; reason: Definition 3.2 quantifies over all $s_{\mathrm{init}}\in\mathcal S$; the inventory vectors on $A_{t_{\mathrm{init}}}$ are among them
--   - generalization: chasable for the policy collection $\Gamma$ → chasable for the set of all feasible pricing policies; reason: implies chasability for every collection $\Gamma$ of feasible policies
--   - generalization: ties broken by the lexicographic order on $A_t$ → ties broken by an arbitrary injective rank on bundles; reason: every lexicographic order is induced by an injective rank, so the statement specializes to the source's
--   - encoding: resources $[N]$, vectors indexed by $A_t$, prices in $(0,1]^{A_t}$ → resources are a finite set of natural numbers, inventory vectors $\mathbb N\to\mathbb N$ equal to $0$ off $A_t$, price vectors $\mathbb N\to\mathbb R$ with values in $(0,1]$ at every resource; reason: changes no demand set, payment or inventory
-- source:
--   Emek, Lavi, Niazadeh, Shi, Stateful Posted Pricing with Vanishing Regret via Dynamic Deterministic Markov Decision Processes, arXiv:2005.01869v2, Theorem 3.6, p.10

import Mathlib
import Definitions.Def_StatefulPricing_DdMDP
import Definitions.Def_StatefulPricing_ChasingOracle
import Definitions.Def_StatefulPricing_Instance
import Definitions.Def_StatefulPricing_Instance_toDdMDP

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace StatefulPricing

/-- **Theorem 3.6** (arXiv:2005.01869v2, p.10): "The Dd-MDPs corresponding to T-round DRACC instances
with arbitrary valuation functions are O(T^{CW/(CW+1)})-chasable."

There is an absolute constant `K₀` such that for all `C`, `W`, `T` and every injective
tie-breaking rank there is one randomized online chasing oracle `O` (chosen before the instance)
which, on the Dd-MDP of every DRACC instance with horizon `T` and bounds `C`, `W`, is
`K₀ · T^{CW/(CW+1)}`-chasable for the set of all feasible policies. -/
theorem theorem_3_6 :
    ∃ K₀ : ℝ, ∀ (C W T : ℕ) (rank : Finset ℕ → ℕ), Function.Injective rank →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
        ∃ O : ChasingOracle Ω (Finset ℕ × (ℕ → ℕ)) (ℕ → ℝ), ∀ I : Instance T C W,
          O.IsChasable P (I.toDdMDP rank) T (K₀ * (T : ℝ) ^ ((C * W : ℝ) / (C * W + 1)))
            {γ | (I.toDdMDP rank).IsPolicy γ} := by sorry

end StatefulPricing
