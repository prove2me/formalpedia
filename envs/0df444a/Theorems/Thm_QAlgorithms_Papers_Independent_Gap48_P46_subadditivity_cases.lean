-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P46_subadditivity_cases
-- name    : QAlgorithms.Papers.Independent.Gap48.P46.subadditivity_cases
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:55:44.206959+00:00
-- url     : https://prove2.me/theorems/eb154cc6-8e4b-44bd-b586-c56ac5630c1d
-- title:
--   Proposition 2: three subadditivity cases
-- statement:
--   All quantum systems are nonzero finite-dimensional complex Hilbert spaces. States are positive semidefinite trace-one matrices, and channels are CPTP maps on the full matrix algebra. All entropies and logarithms are in bits. An ensemble is a finite probability distribution of states, with zero weights permitted. For a channel $\Phi$, write $\chi_\Phi(\rho)$ for the maximum ensemble Holevo information at mean $\rho$, $\widehat H_\Phi(\rho)$ for the minimum average output entropy at that mean, and $\overline C(\Phi;\mathcal A)$ for the maximum of $\chi_\Phi$ over a nonempty closed mean constraint $\mathcal A$.
--
--   Fix any channel $\Psi$. Pointwise chi subadditivity means
--
--   $$\chi_{\Phi\otimes\Psi}(\sigma)\le\chi_\Phi(\operatorname{Tr}_K\sigma)+\chi_\Psi(\operatorname{Tr}_H\sigma)\qquad\text{for every joint state }\sigma.$$
--
--   It holds in each of these cases: $\Phi$ is the identity channel; $\Phi$ is entanglement breaking, meaning that every finite reference extension maps densities to separable states; or $\Phi=q\operatorname{Id}\oplus(1-q)\Phi_0$ for $q\in[0,1]$, where $\Phi_0$ and $\Psi$ already satisfy the displayed property. This gives all three channel classes stated by the proposition.
-- source:
--   On Shor's channel extension and constrained channels, arXiv:quant-ph/0306196v2, PDF p. 8, Proposition 2: three subadditivity cases

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

/-- PDF pp.8–10, Proposition 2: noiseless, entanglement-breaking, and noiseless
mixture cases. IsEB is the accepted dimension-general predicate. -/
theorem subadditivity_cases [Nonempty I] [Nonempty O] [Nonempty J] [Nonempty K]
    (Psi : Superop J K) (hPsi : IsChannel Psi) :
    ChiSubadditive (id : Superop I I) Psi ∧
    (∀ Phi : Superop I O, IsChannel Phi → IsEB Phi → ChiSubadditive Phi Psi) ∧
    (∀ Phi : Superop I O, IsChannel Phi → ChiSubadditive Phi Psi →
      ∀ q ∈ Set.Icc (0 : ℝ) 1, ChiSubadditive (twoBranchFlaggedChannel q (id : Superop I I) Phi) Psi) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P46

end
