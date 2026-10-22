-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P46_partial_trace_scope
-- name    : QAlgorithms.Papers.Independent.Gap48.P46.partial_trace_scope
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:56:27.958851+00:00
-- url     : https://prove2.me/theorems/1e808f58-19c3-4a0b-b074-228db372500d
-- title:
--   Remark 1: partial traces and global additivity
-- statement:
--   All quantum systems are nonzero finite-dimensional complex Hilbert spaces. States are positive semidefinite trace-one matrices, and channels are CPTP maps on the full matrix algebra. All entropies and logarithms are in bits. An ensemble is a finite probability distribution of states, with zero weights permitted. For a channel $\Phi$, write $\chi_\Phi(\rho)$ for the maximum ensemble Holevo information at mean $\rho$, $\widehat H_\Phi(\rho)$ for the minimum average output entropy at that mean, and $\overline C(\Phi;\mathcal A)$ for the maximum of $\chi_\Phi$ over a nonempty closed mean constraint $\mathcal A$. The constraint $\mathcal A\otimes\mathcal B$ includes every joint density with first marginal in $\mathcal A$ and second marginal in $\mathcal B$, including correlated and entangled states.
--
--   Unconstrained chi-capacity additivity holds for every pair of partial-trace channels. Moreover, if additivity holds for every pair of finite-dimensional partial-trace channels with every nonempty closed marginal constraint pair, then it holds for every pair of unconstrained channels:
--
--   $$\bigl[\text{all constrained partial-trace pairs are additive}\bigr]\ \Longrightarrow\ \bigl[\text{all unconstrained channel pairs are additive}\bigr].$$
--
--   Both clauses of the remark compare the scope of additivity assertions; constrained additivity is not asserted unconditionally.
-- source:
--   On Shor's channel extension and constrained channels, arXiv:quant-ph/0306196v2, PDF p. 8, Remark 1: partial traces and global additivity

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P46

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits)

open QAlgorithms.Papers.Independent.Dependency50.P23 (IsEB)

open QAlgorithms.Papers.Independent.Information100.P08
  (Ensemble ensembleAverage outputHolevo mixedRoof)

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- PDF p.8, Remark 1: unconstrained partial-trace additivity, and the implication
from globally constrained partial-trace additivity to global unconstrained additivity. -/
theorem partial_trace_scope [Nonempty I] [Nonempty O] [Nonempty J] [Nonempty K] :
    ConstrainedAdditive (traceRight : Superop (I × O) I) (traceRight : Superop (J × K) J)
      (states (I × O)) (states (J × K)) ∧
    (PartialTraceConstrained → GlobalUnconstrained) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P46

end
