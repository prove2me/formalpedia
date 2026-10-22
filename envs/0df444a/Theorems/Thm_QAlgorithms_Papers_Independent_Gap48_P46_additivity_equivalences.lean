-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P46_additivity_equivalences
-- name    : QAlgorithms.Papers.Independent.Gap48.P46.additivity_equivalences
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:52:15.297546+00:00
-- url     : https://prove2.me/theorems/ef9f92a7-2194-4445-a7c9-1b4207737c16
-- title:
--   Theorem 1: four equivalent additivity properties
-- statement:
--   All quantum systems are nonzero finite-dimensional complex Hilbert spaces. States are positive semidefinite trace-one matrices, and channels are CPTP maps on the full matrix algebra. All entropies and logarithms are in bits. An ensemble is a finite probability distribution of states, with zero weights permitted. For a channel $\Phi$, write $\chi_\Phi(\rho)$ for the maximum ensemble Holevo information at mean $\rho$, $\widehat H_\Phi(\rho)$ for the minimum average output entropy at that mean, and $\overline C(\Phi;\mathcal A)$ for the maximum of $\chi_\Phi$ over a nonempty closed mean constraint $\mathcal A$. The constraint $\mathcal A\otimes\mathcal B$ includes every joint density with first marginal in $\mathcal A$ and second marginal in $\mathcal B$, including correlated and entangled states.
--
--   Fix channels $\Phi$ and $\Psi$. The following six universally quantified properties are equivalent:
--
--   1. For all nonempty closed $\mathcal A,\mathcal B$, $\overline C(\Phi\otimes\Psi;\mathcal A\otimes\mathcal B)=\overline C(\Phi;\mathcal A)+\overline C(\Psi;\mathcal B)$.
--   2. The same identity holds for all nonempty positive-observable linear inequality constraints with nonnegative budgets.
--   3. For every joint state $\sigma$, with $\sigma^\Phi=\operatorname{Tr}_K\sigma$ and $\sigma^\Psi=\operatorname{Tr}_H\sigma$,
--
--   $$\chi_{\Phi\otimes\Psi}(\sigma)\le\chi_\Phi(\sigma^\Phi)+\chi_\Psi(\sigma^\Psi).$$
--
--   4. For every joint state, $\widehat H_{\Phi\otimes\Psi}(\sigma)\ge\widehat H_\Phi(\sigma^\Phi)+\widehat H_\Psi(\sigma^\Psi)$.
--   5. For all states $\rho,\omega$, $\chi_{\Phi\otimes\Psi}(\rho\otimes\omega)=\chi_\Phi(\rho)+\chi_\Psi(\omega)$.
--   6. For all states $\rho,\omega$, $\widehat H_{\Phi\otimes\Psi}(\rho\otimes\omega)=\widehat H_\Phi(\rho)+\widehat H_\Psi(\omega)$.
--
--   These are equivalences of properties of a fixed pair, not unconditional additivity claims.
-- source:
--   On Shor's channel extension and constrained channels, arXiv:quant-ph/0306196v2, PDF p. 6, Theorem 1: four equivalent additivity properties

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

/-- PDF pp.6–7, Theorem 1, including the product-state continuation: six equivalent
properties of the fixed pair. No unconditional additivity is asserted. -/
theorem additivity_equivalences [Nonempty I] [Nonempty O] [Nonempty J] [Nonempty K]
    (Phi : Superop I O) (Psi : Superop J K) (hPhi : IsChannel Phi) (hPsi : IsChannel Psi) :
    (AllConstraints Phi Psi ↔ LinearAdditive Phi Psi) ∧
    (AllConstraints Phi Psi ↔ ChiSubadditive Phi Psi) ∧
    (AllConstraints Phi Psi ↔ RoofSuperadditive Phi Psi) ∧
    (AllConstraints Phi Psi ↔ ProductChiAdditive Phi Psi) ∧
    (AllConstraints Phi Psi ↔ ProductRoofAdditive Phi Psi) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P46

end
