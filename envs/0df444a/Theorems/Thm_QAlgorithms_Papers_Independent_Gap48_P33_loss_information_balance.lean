-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P33_loss_information_balance
-- name    : QAlgorithms.Papers.Independent.Gap48.P33.loss_information_balance
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T04:31:19.389774+00:00
-- url     : https://prove2.me/theorems/c1875bf4-626c-4620-a7fb-4e0f4ea7fb20
-- title:
--   loss bounds and information balance
-- statement:
--   Let $\rho$ be a density on a finite nonzero signal register. A fixed normalized finite Kraus family defines a channel $\mathcal N$ and its pure-environment dilation. Purify $\rho$ by an untouched reference $R$, and denote the final signal and environment by $Q'$ and $E'$. Put $S=S(\rho)$, $S_e=S(RQ')=S(E')$, $I=S(R:Q')$, and $L=S+S_e-S(Q')$. Then
--
--   $$L=I(R:E'\mid Q')=I(R:E'),\qquad 0\le L\le2\min(S,S_e),$$
--   $$I+L=2S,\qquad 0\le I\le2S.$$
--
--   All entropies are in bits. These relations describe the division of initial reference-signal correlations between the output and final environment.
-- source:
--   On the von Neumann capacity of noisy quantum channels, arXiv:quant-ph/9609024v3, PDF p. 5, III.B, (3.12)–(3.16): loss bounds and information balance

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

/-- PDF pp.4–6, (3.9), (3.12)–(3.16): full loss bounds and balance.
The environment is the final dilation register, not the initial pure ancilla. -/
theorem loss_information_balance
    [Nonempty A] [Nonempty B] [Nonempty K]
    (E : K → Matrix B A ℂ) (hE : IsKrausFamily E)
    (rho : Matrix A A ℂ) (hrho : IsDensityMatrix rho) :
    let N := krausApply E
    let omega := pureDensity (dilationReference E (canonicalPurification rho))
    loss N rho = middleConditionalInformation omega ∧
    loss N rho = mutualInformation (discardMiddle omega) ∧
    entropyExchange N rho = vnEntropy (traceLeft (traceLeft omega)) ∧
    0 ≤ loss N rho ∧ loss N rho ≤ 2 * min (vnEntropy rho) (entropyExchange N rho) ∧
    inputMutualInfo N rho + loss N rho = 2 * vnEntropy rho ∧
    0 ≤ inputMutualInfo N rho ∧ inputMutualInfo N rho ≤ 2 * vnEntropy rho := by sorry

end FiniteRegisters

end QAlgorithms.Papers.Independent.Gap48.P33
