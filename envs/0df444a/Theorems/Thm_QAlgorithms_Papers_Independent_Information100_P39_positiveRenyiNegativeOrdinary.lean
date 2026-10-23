-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P39_positiveRenyiNegativeOrdinary
-- name    : QAlgorithms.Papers.Independent.Information100.P39.positiveRenyiNegativeOrdinary
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:19:41.117326+00:00
-- url     : https://prove2.me/theorems/76ad8aaa-f37f-40f7-9887-e4d306370fde
-- title:
--   Unnumbered separation example, author note [44]
-- statement:
--   Consider the trivial one-qubit code with depolarizing Pauli law $(7/10,1/10,1/10,1/10)$ in the order $(I,X,Y,Z)$. Let $J$ be its normalized noisy Choi state. The syndrome has one possible value, so matched-syndrome postselection accepts with probability one and has the same Choi state with a trivial flag. Its ordinary coherent information therefore satisfies
--
--   $$I_{c,\mathrm{match}}=I_c^{(1)}
--   =\log2+\tfrac7{10}\log\tfrac7{10}+\tfrac3{10}\log\tfrac1{10}<0,
--   \qquad I_c^{(2)}=\log\tfrac{26}{25}>0.$$
--
--   All logarithms are natural. This exact example separates positivity of a finite-order Rényi quantity from positivity of the matched channel's ordinary coherent information.
-- source:
--   Hierarchy of Rényi Coherent Information in Stabilizer Codes, arXiv:2609.11930v1, PDF p. 7, Unnumbered separation example, author note [44]

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P39

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable

/-- PDF p.7, note [44]: the trivial one-qubit code, p=3/10. With one syndrome,
matching leaves the original channel and Choi state unchanged. -/
theorem positiveRenyiNegativeOrdinary :
    ∃ hnu : Learning.IsDistribution (depolarizingLaw (3/10)),
      let J := noisyChoi (1 : Matrix (Qubits 1) (Qubits 1) ℂ)
        (depolarizingLaw (3/10)) hnu
      coherentInformation 1 (singleSyndromeState J) = coherentInformation 1 J ∧
      coherentInformation 2 J = Real.log (26/25) ∧
      coherentInformation 1 J = Real.log 2 + (7/10)*Real.log (7/10) +
        (3/10)*Real.log (1/10) ∧
      0 < coherentInformation 2 J ∧ coherentInformation 1 J < 0 := by sorry

end QAlgorithms.Papers.Independent.Information100.P39

end
