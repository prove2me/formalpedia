-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P19_entangled_superdense
-- name    : QAlgorithms.Papers.Independent.Support21.P19.entangled_superdense
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T05:10:33.309335+00:00
-- url     : https://prove2.me/theorems/efde384c-ac3c-40ef-bd35-13249ad92603
-- title:
--   Superdense coding of entangled quantum states
-- statement:
--   For a normalized finite ensemble $\mathcal E=\{p_i,|\psi_i\rangle_{AB}\}$, let $E$ be its average entanglement entropy and $\chi$ the Holevo information of Bob's reduced ensemble, both in bits. Then
--
--   $$
--   \frac\chi2\,[q\to q]+\left(E+\frac\chi2\right)[qq]\ge\mathcal E\qquad(a).
--   $$
--
--   The target is coherent controlled preparation on the full probability-typical sequence span, preserving Alice's labels and arbitrary reference entanglement. For all positive error, rate and typicality slacks, the claimed rates are attained by integer resource counts for all sufficiently large block lengths. The asymptotic interpretation follows from Eq. (7). This extends superdense coding to entangled quantum states.
-- source:
--   Coherent Communication of Classical Messages, arXiv:quant-ph/0307091v3, PDF p. 4, Superdense coding of entangled quantum states

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P19

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4: superdense coding of the same coherent typical-subspace ensemble task.
The asymptotic marker is inherited from Eq. (7). -/
theorem entangled_superdense {a b : ℕ} (E : BipartitePureData a b) :
    Prepares E (bobHolevoBits E.prob E.vector/2) 0 (averageE E.prob E.vector+bobHolevoBits E.prob E.vector/2) := by sorry

end QAlgorithms.Papers.Independent.Support21.P19

end
