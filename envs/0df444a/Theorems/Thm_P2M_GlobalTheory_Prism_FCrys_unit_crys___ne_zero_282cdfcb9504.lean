-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Prism_FCrys_unit_crys___ne_zero_282cdfcb9504
-- name    : P2M_GlobalTheory_Prism_FCrys_unit_crys___ne_zero_282cdfcb9504
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:06:30.687057+00:00
-- url     : https://prove2.me/theorems/f0be5079-c179-53d2-9fa7-7f8692fdd446
-- title:
--   P2 M Global Theory Prism FCrys unit crys   ne zero 282cdfcb9504: P2 M Global Theory Prism FCrys unit crys   ne zero 282cdfcb9504
-- statement:
--   The P2 M Global Theory Prism FCrys unit crys   ne zero 282cdfcb9504 construction uses the P2 M Global Theory Prism FCrys unit crys   ne zero 282cdfcb9504 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/InvertibleSpanSingleton.lean#L338-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/InvertibleSpanSingleton.lean#L338-L346

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InvertibleSpanSingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Prism
attribute [instance] Obj.ring
variable {l : ℕ} {R : Type} [CommRing R]
attribute [instance] FCrys.acg FCrys.mod
attribute [instance] VBun.acg VBun.mod

theorem P2M_GlobalTheory_Prism_FCrys_unit_crys___ne_zero_282cdfcb9504 (l : ℕ) [hl : Fact l.Prime] :
    (FCrys.unit l ℤ_[l]).Φ (Obj.crys l) ⟨(l : ℤ_[l]), Ideal.mem_span_singleton_self _⟩ (1 : ℤ_[l]) ≠ 0 := by sorry

alias «GlobalTheory».«Prism».«FCrys».«unit_crys_Φ_ne_zero» := P2M_GlobalTheory_Prism_FCrys_unit_crys___ne_zero_282cdfcb9504
