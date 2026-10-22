-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P46_shor_capacity_bound
-- name    : QAlgorithms.Papers.Independent.Gap48.P46.shor_capacity_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:58:07.280087+00:00
-- url     : https://prove2.me/theorems/4c897c9e-b5c4-407a-90d0-0e2674337ac5
-- title:
--   Proposition 3: absolute capacity approximation bound
-- statement:
--   All quantum systems are nonzero finite-dimensional complex Hilbert spaces. States are positive semidefinite trace-one matrices, and channels are CPTP maps on the full matrix algebra. All entropies and logarithms are in bits. An ensemble is a finite probability distribution of states, with zero weights permitted. For a channel $\Phi$, write $\chi_\Phi(\rho)$ for the maximum ensemble Holevo information at mean $\rho$, $\widehat H_\Phi(\rho)$ for the minimum average output entropy at that mean, and $\overline C(\Phi;\mathcal A)$ for the maximum of $\chi_\Phi$ over a nonempty closed mean constraint $\mathcal A$.
--
--   Let $\Phi:H\to H'$ and $\Psi:K\to K'$ be channels, and let $\mathcal B$ be a nonempty closed constraint on the second input. For $0\le E\le I$, $q\in[0,1]$, and integer $d\ge1$, put $S_{\mathcal B}=\{\sigma:\operatorname{Tr}_H\sigma\in\mathcal B\}$, where $\sigma$ ranges over joint densities. Then
--
--   $$\left|\overline C(\widehat\Phi(E,q,d)\otimes\Psi;S_{\widehat\Phi}\otimes\mathcal B)-\max_{\sigma\in S_{\mathcal B}}\left[(1-q)\chi_{\Phi\otimes\Psi}(\sigma)+q\log_2d\,\operatorname{Tr}(\sigma(E\otimes I_K))\right]\right|\le q(\log_2\dim K'+1).$$
--
--   Here $S_{\widehat\Phi}$ is the full state space of the extended input, and the displayed maximum is attained. The absolute value gives the source's two-sided approximation bound.
-- source:
--   On Shor's channel extension and constrained channels, arXiv:quant-ph/0306196v2, PDF p. 11, Proposition 3: absolute capacity approximation bound

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

/-- PDF pp.11–13, Proposition 3: absolute approximation and attained maximum.
The absolute-value bars are visible on PDF p.11 but lost in text extraction. -/
theorem shor_capacity_bound [Nonempty I] [Nonempty O] [Nonempty J] [Nonempty K]
    (Phi : Superop I O) (Psi : Superop J K) (hPhi : IsChannel Phi) (hPsi : IsChannel Psi)
    (B : Set (Matrix J J ℂ)) (hB : Constraint B) (E : Matrix I I ℂ) (hE : IsEffect E)
    (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) (d : ℕ) (hd : 1 ≤ d) :
    let S := secondConstraint (I := I) B
    let f := finiteTilt Phi Psi E q d
    |constrainedChiCapacity (tensorChannel (shor Phi E q d) Psi)
        (secondConstraint (I := I × Fin d) B) - maxValue S f| ≤
      q * (Real.logb 2 (Fintype.card K) + 1) ∧ MaximizesValue S f (maxValue S f) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P46

end
