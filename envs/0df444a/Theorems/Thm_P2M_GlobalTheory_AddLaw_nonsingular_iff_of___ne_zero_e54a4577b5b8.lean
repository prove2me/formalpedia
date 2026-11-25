-- Prove2me | Theorems.Thm_P2M_GlobalTheory_AddLaw_nonsingular_iff_of___ne_zero_e54a4577b5b8
-- name    : P2M_GlobalTheory_AddLaw_nonsingular_iff_of___ne_zero_e54a4577b5b8
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:02:28.261798+00:00
-- url     : https://prove2.me/theorems/ec143758-1d8c-4576-a9ac-d0de9e8214b2
-- title:
--   P2 M Global Theory Add Law nonsingular iff of   ne zero e54a4577b5b8: P2 M Global Theory Add Law nonsingular iff of   ne zero e54a4577b5b8
-- statement:
--   The P2 M Global Theory Add Law nonsingular iff of   ne zero e54a4577b5b8 construction uses the P2 M Global Theory Add Law nonsingular iff of   ne zero e54a4577b5b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/AddXYZOrChordXYZOrOriginXYZNeZero.lean#L110-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/AddXYZOrChordXYZOrOriginXYZNeZero.lean#L110-L121

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DiagZEqNegAddY
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SubMulOriginD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open WeierstrassCurve WeierstrassCurve.Projective
open GlobalTheory GlobalTheory.AddLaw
variable {F : Type*} [Field F] {W : Projective F}

theorem P2M_GlobalTheory_AddLaw_nonsingular_iff_of___ne_zero_e54a4577b5b8 (hΔ : W.Δ ≠ 0) (P : Fin 3 → F) :
    W.Nonsingular P ↔ W.Equation P ∧ P ≠ 0 := by sorry

alias «GlobalTheory».«AddLaw».«nonsingular_iff_of_Δ_ne_zero» := P2M_GlobalTheory_AddLaw_nonsingular_iff_of___ne_zero_e54a4577b5b8
