-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P46_global_unconstrained_iff_constrained
-- name    : QAlgorithms.Papers.Independent.Gap48.P46.global_unconstrained_iff_constrained
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:00:58.859101+00:00
-- url     : https://prove2.me/theorems/34cf0b62-5947-40dc-aef5-fb61e23d3f35
-- title:
--   Corollary 3: global unconstrained implies constrained additivity
-- statement:
--   All quantum systems are nonzero finite-dimensional complex Hilbert spaces. States are positive semidefinite trace-one matrices, and channels are CPTP maps on the full matrix algebra. All entropies and logarithms are in bits. An ensemble is a finite probability distribution of states, with zero weights permitted. For a channel $\Phi$, write $\chi_\Phi(\rho)$ for the maximum ensemble Holevo information at mean $\rho$, $\widehat H_\Phi(\rho)$ for the minimum average output entropy at that mean, and $\overline C(\Phi;\mathcal A)$ for the maximum of $\chi_\Phi$ over a nonempty closed mean constraint $\mathcal A$. The constraint $\mathcal A\otimes\mathcal B$ includes every joint density with first marginal in $\mathcal A$ and second marginal in $\mathcal B$, including correlated and entangled states.
--
--   Let global unconstrained additivity mean capacity additivity for every pair of finite-dimensional channels without constraints. Let global constrained additivity mean the corresponding statement for every such pair with every nonempty closed mean constraint pair. Then
--
--   $$\text{global unconstrained additivity}\quad\Longleftrightarrow\quad\text{global constrained additivity}.$$
--
--   The forward implication is Corollary 3; taking full-state constraints gives the converse. Neither conjecture is assumed to hold unconditionally.
-- source:
--   On Shor's channel extension and constrained channels, arXiv:quant-ph/0306196v2, PDF p. 15, Corollary 3: global unconstrained implies constrained additivity

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

/-- PDF p.15, Corollary 3: implication between global conjectures; full-state
constraints supply the reverse implication. -/
theorem global_unconstrained_iff_constrained :
    GlobalUnconstrained ↔ GlobalConstrained := by sorry

end QAlgorithms.Papers.Independent.Gap48.P46

end
