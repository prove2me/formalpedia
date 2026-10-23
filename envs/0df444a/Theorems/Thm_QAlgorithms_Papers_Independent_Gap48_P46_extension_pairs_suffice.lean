-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P46_extension_pairs_suffice
-- name    : QAlgorithms.Papers.Independent.Gap48.P46.extension_pairs_suffice
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:00:14.197078+00:00
-- url     : https://prove2.me/theorems/640bfc6d-5ba8-426d-9560-0ed922228e09
-- title:
--   Corollary 2: two unconstrained extension families suffice
-- statement:
--   All quantum systems are nonzero finite-dimensional complex Hilbert spaces. States are positive semidefinite trace-one matrices, and channels are CPTP maps on the full matrix algebra. All entropies and logarithms are in bits. An ensemble is a finite probability distribution of states, with zero weights permitted. For a channel $\Phi$, write $\chi_\Phi(\rho)$ for the maximum ensemble Holevo information at mean $\rho$, $\widehat H_\Phi(\rho)$ for the minimum average output entropy at that mean, and $\overline C(\Phi;\mathcal A)$ for the maximum of $\chi_\Phi$ over a nonempty closed mean constraint $\mathcal A$. The constraint $\mathcal A\otimes\mathcal B$ includes every joint density with first marginal in $\mathcal A$ and second marginal in $\mathcal B$, including correlated and entangled states.
--
--   Fix channels $\Phi,\Psi$. Suppose unconstrained capacity additivity holds for $\widehat\Phi(E,q,d)$ and $\widehat\Psi(F,r,e)$ for every pair of effects $E,F$, every $q,r\in[0,1]$ and every pair of positive integers $d,e$. Then, for every nonempty closed $\mathcal A,\mathcal B$,
--
--   $$\overline C(\Phi\otimes\Psi;\mathcal A\otimes\mathcal B)=\overline C(\Phi;\mathcal A)+\overline C(\Psi;\mathcal B).$$
--
--   The extension parameters are universally quantified before the conclusion over original constraints. The result reduces constrained additivity of the pair to all its unconstrained extension pairs.
-- source:
--   On Shor's channel extension and constrained channels, arXiv:quant-ph/0306196v2, PDF p. 15, Corollary 2: two unconstrained extension families suffice

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

/-- PDF p.15, Corollary 2: the premise covers every pair of extension parameters,
and the conclusion covers every closed mean constraint pair. -/
theorem extension_pairs_suffice [Nonempty I] [Nonempty O] [Nonempty J] [Nonempty K]
    (Phi : Superop I O) (Psi : Superop J K) (hPhi : IsChannel Phi) (hPsi : IsChannel Psi)
    (h : ∀ E : Matrix I I ℂ, IsEffect E → ∀ F : Matrix J J ℂ, IsEffect F →
      ∀ q ∈ Set.Icc (0 : ℝ) 1, ∀ r ∈ Set.Icc (0 : ℝ) 1,
      ∀ d : ℕ, 1 ≤ d → ∀ e : ℕ, 1 ≤ e →
        ConstrainedAdditive (shor Phi E q d) (shor Psi F r e) (states (I × Fin d)) (states (J × Fin e))) :
    AllConstraints Phi Psi := by sorry

end QAlgorithms.Papers.Independent.Gap48.P46

end
