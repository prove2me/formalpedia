-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P90_bellQber_constraints
-- name    : QAlgorithms.Papers.Independent.Intake100.P90.bellQber_constraints
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:10:28.480821+00:00
-- url     : https://prove2.me/theorems/ebdcfca6-29e7-4515-b8c7-8c66cfdb49d8
-- title:
--   Universal Bell-diagonal QBER coefficient relations
-- statement:
--   Let $\lambda_1,\ldots,\lambda_4\ge0$ sum to one, in the source's order $(\Phi^+,\Phi^-,\Psi^+,\Psi^-)$. Measure the Bell-diagonal density matrix $\sigma=\sum_i\lambda_iP_{\Phi_i}$ in the computational basis on Alice and Bob, and let $Q$ be the actual probability that their outcomes disagree. Then
--
--   $$Q=\lambda_3+\lambda_4,\qquad \lambda_1=1-Q-\lambda_2,\qquad \lambda_4=Q-\lambda_3.$$
--
--   These universal relations apply in particular to the normalized output in $\mathcal D_2[\mathcal D_1(\Gamma_{\mathrm{QBER}})]$. Additional protocol constraints from $\mathcal D_1$ remain in force; the relations do not characterize all attainable attacks.
-- source:
--   Lower and upper bounds on the secret key rate for QKD protocols using one--way classical communication, arXiv:quant-ph/0410215v2, PDF p. 3, Unnumbered two-qubit Bell/QBER parameter reduction

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P90

noncomputable section

open scoped ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P90

/-- PDF p.3: the two universal Bell/QBER relations. Additional restrictions
from the protocol's D1 remain possible; this is not a feasible-set converse. -/
theorem bellQber_constraints (w : Fin 4 → ℝ)
    (hw : ∀ l, 0 ≤ w l) (hsum : ∑ l, w l = 1) :
    let Q := sourceZDisagreement (sourceBellDiagonal w)
    Q = w 2 + w 3 ∧ w 0 = 1 - Q - w 1 ∧ w 3 = Q - w 2 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P90

end
