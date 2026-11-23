-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Prism_Delta_map___of_map___51a3f1233256
-- name    : P2M_GlobalTheory_Prism_Delta_map___of_map___51a3f1233256
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:37.764156+00:00
-- url     : https://prove2.me/theorems/d47a6eff-153a-47c8-9a06-dac1f1d424f0
-- title:
--   P2 M Global Theory Prism Delta map   of map   51a3f1233256: P2 M Global Theory Prism Delta map   of map   51a3f1233256
-- statement:
--   The P2 M Global Theory Prism Delta map   of map   51a3f1233256 construction uses the P2 M Global Theory Prism Delta map   of map   51a3f1233256 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/InvertibleSpanSingleton.lean#L166-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/InvertibleSpanSingleton.lean#L166-L172

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

theorem P2M_GlobalTheory_Prism_Delta_map___of_map___51a3f1233256 {A B : Type} [CommRing A] [CommRing B] (D : Delta l A) (D' : Delta l B)
    (htf : ∀ x : B, (l : B) * x = 0 → x = 0) (f : A →+* B) (h : ∀ a, f (D.φ a) = D'.φ (f a)) (a : A) :
    f (D.δ a) = D'.δ (f a) := by sorry

alias «GlobalTheory».«Prism».«Delta».«map_δ_of_map_φ» := P2M_GlobalTheory_Prism_Delta_map___of_map___51a3f1233256
