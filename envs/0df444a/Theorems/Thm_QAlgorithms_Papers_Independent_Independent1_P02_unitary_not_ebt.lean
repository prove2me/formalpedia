-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P02_unitary_not_ebt
-- name    : QAlgorithms.Papers.Independent.Independent1.P02.unitary_not_ebt
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:17:54.009061+00:00
-- url     : https://prove2.me/theorems/60f3db17-b0a6-481e-9898-6d98804fe78c
-- title:
--   Introduction: unitary conjugation does not break entanglement
-- statement:
--   Let $d\ge2$ and let $U$ be a unitary matrix on $\mathbb C^d$. Then
--
--   $$X\longmapsto UXU^\dagger\quad\text{is not EBT}.$$
--
--   This records that unitary dynamics preserves some entanglement. The dimension restriction corrects the printed sentence: at $d=1$ unitary conjugation is EBT. The correction requires independent source moderation.
--
--   **Correction to the printed source.**
--
--   Printed: Conjugation with a unitary matrix is not EBT, without any stated dimension exception.
--
--   Corrected: Restrict the unitary-channel assertion to d at least two.
--
--   Reason: At d=1 every joint state is separable across the one-dimensional acted-on system; the identity channel is EBT.
-- source:
--   General Entanglement Breaking Channels, arXiv:quant-ph/0302031v2, Introduction: unitary conjugation does not break entanglement, PDF p. 2. https://arxiv.org/abs/quant-ph/0302031v2 . PDF SHA-256: b9741af8740a74b5771c71520597f0a6ee2fa27a7ab56de59ddd399c4f49c465.

import Definitions.Def_QAlgorithms_Defs_HolevoMatrixMaps
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P02_Model
set_option autoImplicit false

/-!
# Entanglement Breaking Channels (quant-ph/0302031v2)

All reference factors occur first. General EB uses the separable positive cone;
EBT additionally preserves trace. Proposed source corrections below require
independent source moderation; see MODERATION_NOTES.md in the assigned unit.
-/

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P02




















































/-- Introduction, PDF p.2. Proposed correction: require d≥2; at d=1 unitary
conjugation is EBT. Pending independent source moderation. -/
theorem unitary_not_ebt (d : ℕ) (hd : 2 ≤ d) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    conjugationEndomorphism U ∉ ebtSet d := by sorry

















end QAlgorithms.Papers.Independent.Independent1.P02
