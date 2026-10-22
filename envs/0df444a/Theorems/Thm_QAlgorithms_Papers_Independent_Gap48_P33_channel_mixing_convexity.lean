-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P33_channel_mixing_convexity
-- name    : QAlgorithms.Papers.Independent.Gap48.P33.channel_mixing_convexity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:33:33.356856+00:00
-- url     : https://prove2.me/theorems/ad39b23e-77e1-47e0-86c9-379680f7081f
-- title:
--   convexity under channel mixing
-- statement:
--   Fix a density $\rho$ on a finite nonzero input register. For channels $\mathcal N_j$ with common input and output registers and finite probability weights $w_j$, form the mixture of entire maps $\mathcal N=\sum_jw_j\mathcal N_j$. Then
--
--   $$I(\mathcal N,\rho)\le\sum_jw_j I(\mathcal N_j,\rho).$$
--
--   Here each information is the mutual entropy of the unchanged purifying reference and the channel output. This retains the reference-output correlations required by the source's channel-mixing argument.
-- source:
--   On the von Neumann capacity of noisy quantum channels, arXiv:quant-ph/9609024v3, PDF p. 6, III.C, (3.21): convexity under channel mixing

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P33

namespace QAlgorithms.Papers.Independent.Gap48.P33

open scoped BigOperators Matrix ComplexConjugate

-- Reuse only definitions from the pinned accepted library; no imported theorem is used.

open QAlgorithms.Papers.Independent.Information100.P27 (shannon average labelInformation)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation first both)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange inputMutualInfo)

open QAlgorithms.Papers.Independent.Claimed50.P03 (pauliWeight wordSupport)

section FiniteRegisters

variable {A B C D R K J : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D]

variable [Fintype R] [Fintype K] [Fintype J]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

variable [DecidableEq R] [DecidableEq K] [DecidableEq J]

/-- PDF pp.6–7, (3.21)–(3.22): convexity under mixing entire channels. -/
theorem channel_mixing_convexity
    [Nonempty A] [Nonempty B]
    (rho : Matrix A A ℂ) (hrho : IsDensityMatrix rho)
    (w : J → ℝ) (hw : ProbabilityWeights w)
    (N : J → Superop A B) (hN : ∀ j, IsChannel (N j)) :
    inputMutualInfo (mixedChannel w N) rho ≤ ∑ j, w j * inputMutualInfo (N j) rho := by sorry

end FiniteRegisters

end QAlgorithms.Papers.Independent.Gap48.P33
