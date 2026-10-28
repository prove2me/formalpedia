-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P02_trine_extreme_qc_not_cq
-- name    : QAlgorithms.Papers.Independent.Independent1.P02.trine_extreme_qc_not_cq
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:18:21.103292+00:00
-- url     : https://prove2.me/theorems/cfe6eae2-33f5-4856-9503-4f43d7ffa4f3
-- title:
--   Section 3 Example: a four-dimensional extreme EBT QC map that is not CQ
-- statement:
--   Let $g_0,\ldots,g_3$ and $e_0,\ldots,e_3$ be orthonormal bases of $\mathbb C^4$. Put $g_\pm=(g_0\pm\sqrt3g_1)/2$ and set
--
--   $$F_0=\tfrac23|g_0\rangle\langle g_0|,\quad F_1=\tfrac23|g_+\rangle\langle g_+|,\quad F_2=\tfrac23|g_-\rangle\langle g_-|,\quad F_3=|g_2\rangle\langle g_2|+|g_3\rangle\langle g_3|.$$
--
--   These effects form a POVM, and the computed map $\Phi(X)=\sum_{k=0}^3\operatorname{Tr}(F_kX)|e_k\rangle\langle e_k|$ is an extreme EBT map which is QC and is not CQ.
--
--   The third displayed effect corrects the source's repeated $g_+$ to $g_-$, as forced by the word trine, normalization, and the proof. Independent source moderation is required. This is a concrete witness rather than a free existential channel.
--
--   **Correction to the printed source.**
--
--   Printed: The third effect is printed as (2/3)|g_+><g_+|, duplicating the second.
--
--   Corrected: Replace only that third effect by (2/3)|g_-><g_-|.
--
--   Reason: The narrative calls this a trine POVM and its proof uses that POVM. The changed effect cancels the off-diagonal entries; the printed effects do not sum to I.
-- source:
--   General Entanglement Breaking Channels, arXiv:quant-ph/0302031v2, Section 3 Example: a four-dimensional extreme EBT QC map that is not CQ, PDF p. 8. https://arxiv.org/abs/quant-ph/0302031v2 . PDF SHA-256: b9741af8740a74b5771c71520597f0a6ee2fa27a7ab56de59ddd399c4f49c465.

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




























































/-- Example, PDF pp.8–9. Proposed correction: E_3=(2/3)|g_-⟩⟨g_-|;
the printed duplicate is not a POVM. Pending independent moderation. -/
theorem trine_extreme_qc_not_cq (g e : OrthonormalBasis (Fin 4) ℂ (StateVector 4)) :
    IsPOVM (trineEffects g) ∧ trineEndomorphism g e ∈ (ebtSet 4).extremePoints ℝ ∧
      IsQC (trineEndomorphism g e) ∧ ¬ IsCQ (trineEndomorphism g e) := by sorry









end QAlgorithms.Papers.Independent.Independent1.P02
