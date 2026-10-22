-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P33_measured_input_holevo
-- name    : QAlgorithms.Papers.Independent.Gap48.P33.measured_input_holevo
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:38:46.263104+00:00
-- url     : https://prove2.me/theorems/8c3c9358-c391-4c2e-a15c-eeb8c613ca8d
-- title:
--   measured-input reduction to Holevo information
-- statement:
--   Let orthonormal signal states $|j\rangle$ have finite probability weights $w_j$. Copy the eigenbasis label to classical records $R,X$ as in (4.1), apply a fixed pure-environment channel only to the signal, and discard the other record. Put $\sigma_j=\mathcal N(|j\rangle\langle j|)$, $\bar\sigma=\sum_jw_j\sigma_j$, and $H(w)=-\sum_jw_j\log_2w_j$. Then
--
--   $$I(R:Q')=I(X:Q')=\chi=S(\bar\sigma)-\sum_jw_j S(\sigma_j),$$
--   $$S\!\left(\sum_jw_j|j\rangle\langle j|\right)=H(w)=\chi+I(X:E'\mid Q').$$
--
--   The classical loss $S(XQ')-S(Q')$ equals this conditional mutual information. The two records have the identical cq marginal encoded in Lean. This gives the measured-input reduction to Holevo information.
-- source:
--   On the von Neumann capacity of noisy quantum channels, arXiv:quant-ph/9609024v3, PDF p. 9, IV, (4.7)–(4.8): measured-input reduction to Holevo information

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

/-- PDF pp.9–10, (4.7)–(4.8): the dephased/copied record, not an unmeasured reference.
R and X have identical cq marginals after the other copy is discarded. -/
theorem measured_input_holevo
    [Nonempty A] [Nonempty B] [Nonempty K]
    (E : K → Matrix B A ℂ) (hE : IsKrausFamily E)
    (w : J → ℝ) (hw : ProbabilityWeights w)
    (psi : J → EuclideanSpace ℂ A) (hpsi : Orthonormal ℂ psi) :
    let output := fun j => krausApply E (pureDensity (psi j))
    let joint := cqState w (fun j => pureDensity (dilationVector E (psi j)))
    mutualInformation (cqState w output) = labelInformation w output ∧
    vnEntropy (average w (fun j => pureDensity (psi j))) = shannon w ∧
    shannon w = labelInformation w output + middleConditionalInformation joint ∧
    classicalLoss w output = middleConditionalInformation joint := by sorry

end FiniteRegisters

end QAlgorithms.Papers.Independent.Gap48.P33
