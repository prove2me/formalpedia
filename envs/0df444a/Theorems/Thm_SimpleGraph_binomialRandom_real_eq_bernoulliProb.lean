-- Prove2me | Theorems.Thm_SimpleGraph_binomialRandom_real_eq_bernoulliProb
-- name    : SimpleGraph.binomialRandom_real_eq_bernoulliProb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:00:33.368308+00:00
-- url     : https://prove2.me/theorems/e56a8662-df59-4d27-9826-b013a977d262
-- title:
--   Simple Graph: binomial Random real eq bernoulli Prob
-- statement:
--   The binomial random graph `G(V, p)` gives a set `S` of graphs the probability of any event `Q`
--   on sets of possible edges such that `fromEdgeSet A ∈ S ↔ Q A`.
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/MeasureBridge.lean#L81-L93
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/MeasureBridge.lean#L81-L93

module
public import Definitions.Def_ProbabilisticMethod_RandomGraph
public import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
public import Definitions.Def_ProbabilisticMethod_MeasureBridge
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory unitInterval
open scoped Finset
open SimpleGraph
variable {V : Type*}
variable [Fintype V] [DecidableEq V]

theorem SimpleGraph.binomialRandom_real_eq_bernoulliProb (p : I) {S : Set (SimpleGraph V)}
    {Q : Finset (Sym2 V) → Prop} [DecidablePred Q]
    (hQ : ∀ A ⊆ possibleEdges V, fromEdgeSet (A : Set (Sym2 V)) ∈ S ↔ Q A) :
    G(V, p).real S = (possibleEdges V).bernoulliProb p Q := by sorry
