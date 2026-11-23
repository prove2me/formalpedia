-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Prism_Hom_ext__fc72cc082215
-- name    : P2M_GlobalTheory_Prism_Hom_ext__fc72cc082215
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:33.287282+00:00
-- url     : https://prove2.me/theorems/86b4a7d3-1716-4d76-a162-ff2d3d595953
-- title:
--   P2 M Global Theory Prism Hom ext  fc72cc082215: P2 M Global Theory Prism Hom ext  fc72cc082215
-- statement:
--   The P2 M Global Theory Prism Hom ext  fc72cc082215 construction uses the P2 M Global Theory Prism Hom ext  fc72cc082215 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/InvertibleSpanSingleton.lean#L177-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/InvertibleSpanSingleton.lean#L177-L178

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

theorem P2M_GlobalTheory_Prism_Hom_ext__fc72cc082215 {P P' : Obj l R} {f g : Hom P P'} (h : f.f = g.f) : f = g := by sorry

alias «GlobalTheory».«Prism».«Hom».«ext'» := P2M_GlobalTheory_Prism_Hom_ext__fc72cc082215
