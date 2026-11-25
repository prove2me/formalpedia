-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDim_mem_funField_of_mem_chartRing_f686adb35fde
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDim_mem_funField_of_mem_chartRing_f686adb35fde
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:08:53.687191+00:00
-- url     : https://prove2.me/theorems/c2f7de74-4732-45a9-bcf5-cdd76797ca41
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample Dim mem fun Field of mem chart Ring f686adb35fde: P2 M Ground Theory Heights  Heights Kleiman Very Ample Dim mem fun Field of mem chart Ring f686
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample Dim mem fun Field of mem chart Ring f686adb35fde construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample Dim mem fun Field of mem chart Ring f686adb35fde property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleDim.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleDim.lean#L31-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleDimSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PDimTie
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial AmpleAffineGen
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleDim
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDim_mem_funField_of_mem_chartRing_f686adb35fde {i : Fin (N + 1)} (hi : x i ≠ 0) {a : Ω}
    (ha : a ∈ chartRing k x (singleChart hi)) : a ∈ funField (k := k) x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleDim».«mem_funField_of_mem_chartRing» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDim_mem_funField_of_mem_chartRing_f686adb35fde
