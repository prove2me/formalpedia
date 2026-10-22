-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P46_chi_decomposition
-- name    : QAlgorithms.Papers.Independent.Gap48.P46.chi_decomposition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:49:14.929169+00:00
-- url     : https://prove2.me/theorems/5846ade0-6c22-44af-bb8c-55792a353781
-- title:
--   §2 Eq. (2): chi-function and entropy roof
-- statement:
--   All quantum systems are nonzero finite-dimensional complex Hilbert spaces. States are positive semidefinite trace-one matrices, and channels are CPTP maps on the full matrix algebra. All entropies and logarithms are in bits. An ensemble is a finite probability distribution of states, with zero weights permitted. For a channel $\Phi$, write $\chi_\Phi(\rho)$ for the maximum ensemble Holevo information at mean $\rho$, $\widehat H_\Phi(\rho)$ for the minimum average output entropy at that mean, and $\overline C(\Phi;\mathcal A)$ for the maximum of $\chi_\Phi$ over a nonempty closed mean constraint $\mathcal A$.
--
--   Let $\Phi$ be a channel and $\rho$ a state. With $H$ denoting von Neumann entropy, the independently defined ensemble maximum and entropy minimum satisfy
--
--   $$\chi_\Phi(\rho)=H(\Phi(\rho))-\widehat H_\Phi(\rho).$$
--
--   There exist finite ensembles of mean $\rho$ attaining each of these two extrema. This identifies the entropy-roof decomposition without defining the chi-function through that identity.
-- source:
--   On Shor's channel extension and constrained channels, arXiv:quant-ph/0306196v2, PDF p. 3, §2 Eq. (2): chi-function and entropy roof

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

/-- PDF pp.2–3, Eq.(2): decomposition and attainment of both finite-ensemble extrema. -/
theorem chi_decomposition [Nonempty I] [Nonempty O]
    (Phi : Superop I O) (hPhi : IsChannel Phi) (rho : Matrix I I ℂ)
    (hrho : IsDensityMatrix rho) :
    fixedMeanChi Phi rho = vnEntropy (Phi rho) - (mixedRoof (fun X => vnEntropy (Phi X))) rho ∧
      (∃ e : Ensemble I, (ensembleAverage e) = rho ∧ outputHolevo Phi e = fixedMeanChi Phi rho) ∧
      (∃ e : Ensemble I, (ensembleAverage e) = rho ∧ shorEnsembleEntropy e Phi = (mixedRoof (fun X => vnEntropy (Phi X))) rho) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P46

end
