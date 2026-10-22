-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P46_tilted_capacity_limits
-- name    : QAlgorithms.Papers.Independent.Gap48.P46.tilted_capacity_limits
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:58:54.996318+00:00
-- url     : https://prove2.me/theorems/4eece473-5ad6-422e-a1fe-51505c29c8ac
-- title:
--   §5 Eqs. (25)–(26): tilted capacity limits
-- statement:
--   All quantum systems are nonzero finite-dimensional complex Hilbert spaces. States are positive semidefinite trace-one matrices, and channels are CPTP maps on the full matrix algebra. All entropies and logarithms are in bits. An ensemble is a finite probability distribution of states, with zero weights permitted. For a channel $\Phi$, write $\chi_\Phi(\rho)$ for the maximum ensemble Holevo information at mean $\rho$, $\widehat H_\Phi(\rho)$ for the minimum average output entropy at that mean, and $\overline C(\Phi;\mathcal A)$ for the maximum of $\chi_\Phi$ over a nonempty closed mean constraint $\mathcal A$.
--
--   Let $\Phi:H\to H'$ and $\Psi:K\to K'$ be channels, $\mathcal B$ a nonempty closed second-input constraint, $0\le E\le I$ and $\lambda\ge0$. Along the admissible cofinal tail $d\ge2$, $\lambda\le\log_2d$, set $q_d=\lambda/\log_2d$. Then
--
--   $$\lim_{d\to\infty}\overline C(\widehat\Phi(E,q_d,d))=\max_\rho[\chi_\Phi(\rho)+\lambda\operatorname{Tr}(E\rho)],$$
--
--   $$\lim_{d\to\infty}\overline C(\widehat\Phi(E,q_d,d)\otimes\Psi;S_{\widehat\Phi}\otimes\mathcal B)=\max_{\sigma:\operatorname{Tr}_H\sigma\in\mathcal B}[\chi_{\Phi\otimes\Psi}(\sigma)+\lambda\operatorname{Tr}(\sigma(E\otimes I_K))].$$
--
--   Both maxima are over densities and are attained. Both limits exist without an additivity assumption. Arbitrary zero scalar prefixes encode the same physical-tail limits in the formalization.
-- source:
--   On Shor's channel extension and constrained channels, arXiv:quant-ph/0306196v2, PDF p. 13, §5 Eqs. (25)–(26): tilted capacity limits

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

/-- PDF p.13, Eqs.(25)–(26): both physical-tail limits and attained maxima, without
assuming additivity. Lambda zero is allowed. -/
theorem tilted_capacity_limits [Nonempty I] [Nonempty O] [Nonempty J] [Nonempty K]
    (Phi : Superop I O) (Psi : Superop J K) (hPhi : IsChannel Phi) (hPsi : IsChannel Psi)
    (B : Set (Matrix J J ℂ)) (hB : Constraint B) (E : Matrix I I ℂ) (hE : IsEffect E)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    Tendsto (extensionSequence Phi E lam) atTop (nhds (maxValue (states I) (shorTiltObjective Phi E lam))) ∧
    Tendsto (jointExtensionSequence Phi Psi B E lam) atTop
      (nhds (maxValue (secondConstraint (I := I) B) (jointTilted Phi Psi E lam))) ∧
    MaximizesValue (states I) (shorTiltObjective Phi E lam) (maxValue (states I) (shorTiltObjective Phi E lam)) ∧
    MaximizesValue (secondConstraint (I := I) B) (jointTilted Phi Psi E lam)
      (maxValue (secondConstraint (I := I) B) (jointTilted Phi Psi E lam)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P46

end
