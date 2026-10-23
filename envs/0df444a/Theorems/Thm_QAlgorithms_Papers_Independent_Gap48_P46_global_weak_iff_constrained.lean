-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P46_global_weak_iff_constrained
-- name    : QAlgorithms.Papers.Independent.Gap48.P46.global_weak_iff_constrained
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:04:16.894507+00:00
-- url     : https://prove2.me/theorems/b484922b-4a21-4061-bb76-61c8c3aef782
-- title:
--   §6: global weak and constrained additivity are equivalent
-- statement:
--   All quantum systems are nonzero finite-dimensional complex Hilbert spaces. States are positive semidefinite trace-one matrices, and channels are CPTP maps on the full matrix algebra. All entropies and logarithms are in bits. An ensemble is a finite probability distribution of states, with zero weights permitted. For a channel $\Phi$, write $\chi_\Phi(\rho)$ for the maximum ensemble Holevo information at mean $\rho$, $\widehat H_\Phi(\rho)$ for the minimum average output entropy at that mean, and $\overline C(\Phi;\mathcal A)$ for the maximum of $\chi_\Phi$ over a nonempty closed mean constraint $\mathcal A$.
--
--   Global weak additivity means that the attained allocation identity (33) holds for every finite-dimensional channel pair, every pair of positive observables and every feasible nonnegative total budget. Global constrained additivity means capacity additivity for every finite-dimensional channel pair and every nonempty closed marginal constraint pair. Then
--
--   $$\text{global weak additivity}\quad\Longleftrightarrow\quad\text{global constrained additivity}.$$
--
--   Both sides quantify over all channel pairs; a weak identity for a single pair is not sufficient as a premise. This states the final finite-dimensional equivalence of §6.
-- source:
--   On Shor's channel extension and constrained channels, arXiv:quant-ph/0306196v2, PDF p. 16, §6: global weak and constrained additivity are equivalent

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

/-- PDF p.16, §6: global weak and constrained conjectures are equivalent. A weak
identity for only one fixed pair is not the premise. -/
theorem global_weak_iff_constrained : GlobalWeak ↔ GlobalConstrained := by sorry

end QAlgorithms.Papers.Independent.Gap48.P46

end
