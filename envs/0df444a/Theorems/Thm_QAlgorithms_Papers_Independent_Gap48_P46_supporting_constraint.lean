-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P46_supporting_constraint
-- name    : QAlgorithms.Papers.Independent.Gap48.P46.supporting_constraint
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:49:59.492829+00:00
-- url     : https://prove2.me/theorems/db443c05-bfd3-4c05-9875-dcee5f6af9e8
-- title:
--   Lemma 1: supporting linear constraint
-- statement:
--   All quantum systems are nonzero finite-dimensional complex Hilbert spaces. States are positive semidefinite trace-one matrices, and channels are CPTP maps on the full matrix algebra. All entropies and logarithms are in bits. An ensemble is a finite probability distribution of states, with zero weights permitted. For a channel $\Phi$, write $\chi_\Phi(\rho)$ for the maximum ensemble Holevo information at mean $\rho$, $\widehat H_\Phi(\rho)$ for the minimum average output entropy at that mean, and $\overline C(\Phi;\mathcal A)$ for the maximum of $\chi_\Phi$ over a nonempty closed mean constraint $\mathcal A$.
--
--   Let $\Phi$ be a channel and $\rho_0$ a full-rank state. There is an effect $A$, meaning $0\le A\le I$, such that, on putting $\alpha=\operatorname{Tr}(A\rho_0)$,
--
--   $$\operatorname{Tr}(A\rho)\le\alpha\quad\Longrightarrow\quad\chi_\Phi(\rho)\le\chi_\Phi(\rho_0)$$
--
--   for every state $\rho$. Thus any full-rank state supports a linear constraint under which it maximizes chi. No strict-feasibility conclusion is asserted.
-- source:
--   On Shor's channel extension and constrained channels, arXiv:quant-ph/0306196v2, PDF p. 3, Lemma 1: supporting linear constraint

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

/-- PDF p.3, Lemma 1 (proof pp.16–17): a full-rank density supports an effect
constraint. Strict feasibility and nonscalar effects are not hypotheses. -/
theorem supporting_constraint [Nonempty I] [Nonempty O]
    (Phi : Superop I O) (hPhi : IsChannel Phi) (rho : Matrix I I ℂ)
    (hrho : IsDensityMatrix rho) (hfull : IsUnit rho.det) :
    ∃ A : Matrix I I ℂ, IsEffect A ∧ ∀ omega ∈ states I,
      effectProb A omega ≤ effectProb A rho → fixedMeanChi Phi omega ≤ fixedMeanChi Phi rho := by sorry

end QAlgorithms.Papers.Independent.Gap48.P46

end
