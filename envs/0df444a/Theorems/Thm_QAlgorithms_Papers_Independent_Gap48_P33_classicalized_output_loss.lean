-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P33_classicalized_output_loss
-- name    : QAlgorithms.Papers.Independent.Gap48.P33.classicalized_output_loss
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T04:41:34.203697+00:00
-- url     : https://prove2.me/theorems/1c607e21-2f78-4770-b5a9-0a12c2326672
-- title:
--   classicalized depolarizing output and loss
-- statement:
--   For $p,q\in[0,1]$, copy the q-input eigenbasis to an ancilla, discard that copy, and apply the Pauli channel to the signal. In the printed signal-reference order,
--
--   $$\rho_{Q'R}=(1-2p/3)\bigl[(1-q)|10\rangle\langle10|+q|01\rangle\langle01|\bigr]+(2p/3)\bigl[(1-q)|00\rangle\langle00|+q|11\rangle\langle11|\bigr].$$
--
--   Let $H$ be the Shannon entropy of its four probabilities. The classical loss and mutual information satisfy
--
--   $$L=H\!\left(\frac{2p(1-q)}3,\frac{2pq}3,(1-2p/3)(1-q),(1-2p/3)q\right)-H_2\!\left(q+\frac{2p}3(1-2q)\right),\qquad I=H_2(q)-L.$$
--
--   This loss is conditional record entropy, distinct from the unmeasured quantum loss.
--
--   Here $H_2$ denotes binary Shannon entropy in bits, with $0\log 0=0$.
-- source:
--   On the von Neumann capacity of noisy quantum channels, arXiv:quant-ph/9609024v3, PDF p. 12, V.B, (5.21)–(5.23): classicalized depolarizing output and loss

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

/-- PDF p.12, (5.21)–(5.23): full classicalized output and its distinct loss. -/
theorem classicalized_output_loss (p q : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    classicalOutput p q = Matrix.diagonal (fun rq =>
      (((if rq.1 = rq.2 then 2 * p / 3 else 1 - 2 * p / 3) *
        (if rq.1 then q else 1 - q) : ℝ) : ℂ)) ∧
    measuredLoss p q = shannon (classicalSpectrum p q) -
      binEntropy2 (q + (2 * p / 3) * (1 - 2 * q)) ∧
    mutualInformation (classicalOutput p q) = binEntropy2 q - measuredLoss p q := by sorry

end QAlgorithms.Papers.Independent.Gap48.P33
