-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P19_flaggedProduct_zero
-- name    : QAlgorithms.Papers.Independent.Gap48.P19.flaggedProduct_zero
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:08:26.409474+00:00
-- url     : https://prove2.me/theorems/34fc03eb-46ed-4db1-9b5a-692d40c7444d
-- title:
--   Flagged product states have zero quantum CMI
-- statement:
--   Let $A,B,L$ index nonzero finite complex Hilbert spaces. Let $(w_l)$ be a probability vector, $\rho_A^l$ and $\rho_B^l$ density matrices, and $(|f_l\rangle)$ an arbitrary orthonormal basis of the flag space. Then
--
--   $$\omega_{ABL}=\sum_l w_l\,\rho_A^l\otimes\rho_B^l\otimes |f_l\rangle\langle f_l|$$
--
--   is a density matrix and, using von Neumann entropies in nats,
--
--   $$I_\omega(A:B\mid L)=0.$$
--
--   Zero weights are allowed and every component is normalized, even at a zero weight. The assertion concerns this specified flagged product construction.
-- source:
--   Entanglement of Distillation and Conditional Mutual Information, arXiv:quant-ph/0202144v2, PDF p. 4, §2, Eq.(7)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P19

namespace QAlgorithms.Papers.Independent.Gap48.P19

open scoped ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Information100.P75 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, (7): arbitrary orthonormal flags and normalized product components give zero CMI.
The sign correction of (4) is recorded in the module preamble. -/
theorem flaggedProduct_zero {A B L : Type} [Fintype A] [Fintype B] [Fintype L]
    [DecidableEq A] [DecidableEq B] [DecidableEq L]
    [Nonempty A] [Nonempty B] [Nonempty L]
    (w : L → ℝ) (ra : L → Mat A) (rb : L → Mat B)
    (F : Matrix.unitaryGroup L ℂ) (hw : IsLaw w)
    (ha : ∀ l, IsDensityMatrix (ra l)) (hb : ∀ l, IsDensityMatrix (rb l)) :
    IsDensityMatrix (flaggedProduct w ra rb F) ∧
    extensionQuantumCMI (flaggedProduct w ra rb F) = 0 := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P19
