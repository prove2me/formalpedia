-- Prove2me | Theorems.Thm_RobustMarkovAssort_Duality_proposition_2
-- name    : RobustMarkovAssort.Duality.proposition_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T23:18:33.115288+00:00
-- url     : https://prove2.me/theorems/ce75c277-e1c2-42c8-a287-43a1882590c2
-- title:
--   Proposition 2 — row separation of the dual assortment program
-- statement:
--   For row-product Markov uncertainty and the positive-arrival standing preamble, the joint dual program (5) and separated program (6) have the same attained minimum. This is Assumption 5 for the constructed specialization. No strict-escape or compactness assumption is added.
--
--   Differences from the source:
--   - encoding: products numbered 1 through n and arbitrary subsets of N → products Fin n and assortments Finset (Fin n); reason: the index shift is a bijection and every subset is represented
--   - generalization: a finite universe of products → n may also be zero; reason: the empty universe has one empty vector and one assortment, all revenues are zero, and every claimed extremum and fixed point exists uniquely there
--   - reading: uncertainty sets of possible model parameters → each parameter set is explicitly nonempty; reason: a possible-parameter set is read as containing at least one scenario, consistent with the choice of u0 on page 19
--   - generalization: arrival probabilities in the model description and strictly positive vectors in Assumption 2 → arbitrary strictly positive arrival weights without normalization; reason: the explicit assumption is positivity and all normalized probability instances specialize directly
--   - encoding: Assumption 1 states Cartesian row uncertainty → the model constructs exactly that Cartesian product, independently of arrival uncertainty; reason: the construction ranges over all and only the source scenarios
--   - reading: Proposition 2 names Assumption 1 while its preceding paragraph invokes positive arrivals → MCPositive is explicit and the transition domain retains nonnegativity, zero diagonal and row sums at most one; reason: this records the surrounding Markov conventions and the stated positivity preamble without adding strict escape to Proposition 2
--   - reading: equivalent optimization programs with nested minima in Assumptions 5 and 6 → equal attained least objective values with inner weight minima defined on the relational feasible domain; reason: this makes optimal-value equivalence explicit without requiring pointwise simultaneous optimizers; missing row minima do not receive defaults
--   - encoding: the displayed min and max values → IsLeast and IsGreatest objective-image relations, including every inner extremum; reason: membership expresses attainment and the order bound expresses optimality
-- source:
--   Désir, Goyal, Jiang, Xie and Zhang, Robust Assortment Optimization Under the Markov Chain Choice Model, Operations Research (2023), DOI 10.1287/opre.2022.2420; canonical artifact PDF/printed p. 12, Proposition 2

import Definitions.Def_RobustMarkovAssort_Duality_MCPrograms

namespace RobustMarkovAssort.Duality

theorem proposition_2 {n : ℕ} (M : MCUncertainty n) (hpos : MCPositive M) :
    Assumption5 (specialization M) := by sorry

end RobustMarkovAssort.Duality
