-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P46_shor_extension_channel
-- name    : QAlgorithms.Papers.Independent.Gap48.P46.shor_extension_channel
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:56:57.727301+00:00
-- url     : https://prove2.me/theorems/6dc87295-ae16-4a4c-a04a-67b0e0e6fa57
-- title:
--   §5 and Remark 2: full-algebra Shor extension
-- statement:
--   All quantum systems are nonzero finite-dimensional complex Hilbert spaces. States are positive semidefinite trace-one matrices, and channels are CPTP maps on the full matrix algebra. All entropies and logarithms are in bits. An ensemble is a finite probability distribution of states, with zero weights permitted. For a channel $\Phi$, write $\chi_\Phi(\rho)$ for the maximum ensemble Holevo information at mean $\rho$, $\widehat H_\Phi(\rho)$ for the minimum average output entropy at that mean, and $\overline C(\Phi;\mathcal A)$ for the maximum of $\chi_\Phi$ over a nonempty closed mean constraint $\mathcal A$.
--
--   Let $\Phi$ be a channel, $0\le E\le I$, $q\in[0,1]$, and $d\ge1$ an integer. For an arbitrary operator $X$ on $H\otimes\mathbb C^d$, let $X_{jj}$ be its diagonal label blocks and $\rho=\sum_jX_{jj}$. Define the full-algebra map
--
--   $$\widehat\Phi(E,q,d)(X)=(1-q)\Phi(\rho)\ \oplus\ q\operatorname{diag}\bigl(\operatorname{Tr}((I-E)\rho),\operatorname{Tr}(EX_{11}),\ldots,\operatorname{Tr}(EX_{dd})\bigr).$$
--
--   This map is CPTP and is unchanged when all off-diagonal label blocks of $X$ are deleted. It agrees with the classical-array formula on diagonal arrays, while supplying the full quantum channel required by Remark 2. The cases $d=1$ and $q=0,1$ are included.
-- source:
--   On Shor's channel extension and constrained channels, arXiv:quant-ph/0306196v2, PDF p. 10, §5 and Remark 2: full-algebra Shor extension

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

/-- PDF pp.10–11, §5 and Remark 2: the explicit full-algebra Shor map is CPTP,
and input label dephasing leaves its output unchanged. -/
theorem shor_extension_channel [Nonempty I] [Nonempty O]
    (Phi : Superop I O) (hPhi : IsChannel Phi) (E : Matrix I I ℂ) (hE : IsEffect E)
    (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) (d : ℕ) (hd : 1 ≤ d) :
    IsChannel (shor Phi E q d) ∧ ∀ X,
      shor Phi E q d X = shor Phi E q d (dephaseLabel d X) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P46

end
