-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Prism_Delta___zero_fed7c125f185
-- name    : P2M_GlobalTheory_Prism_Delta___zero_fed7c125f185
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:03.319672+00:00
-- url     : https://prove2.me/theorems/97671527-6ae9-4203-86f4-44864b5bbb7e
-- title:
--   P2 M Global Theory Prism Delta   zero fed7c125f185: P2 M Global Theory Prism Delta   zero fed7c125f185
-- statement:
--   The P2 M Global Theory Prism Delta   zero fed7c125f185 construction uses the P2 M Global Theory Prism Delta   zero fed7c125f185 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/InvertibleSpanSingleton.lean#L112-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/InvertibleSpanSingleton.lean#L112-L118

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

theorem P2M_GlobalTheory_Prism_Delta___zero_fed7c125f185 {A : Type} [CommRing A] (D : Delta l A) : D.δ 0 = 0 := by sorry

alias «GlobalTheory».«Prism».«Delta».«δ_zero» := P2M_GlobalTheory_Prism_Delta___zero_fed7c125f185
