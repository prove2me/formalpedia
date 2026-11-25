-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDim_ampleBase_le_funField_3c18574d4cd9
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDim_ampleBase_le_funField_3c18574d4cd9
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:08:50.126894+00:00
-- url     : https://prove2.me/theorems/ca1e58c5-1e0a-4f4d-ab5d-738b03fed217
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample Dim ample Base le fun Field 3c18574d4cd9: P2 M Ground Theory Heights  Heights Kleiman Very Ample Dim ample Base le fun Field 3c18574d4cd9
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample Dim ample Base le fun Field 3c18574d4cd9 construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample Dim ample Base le fun Field 3c18574d4cd9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleDim.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleDim.lean#L23-L29

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDim_ampleBase_le_funField_3c18574d4cd9 {r : ℕ} (h : Fin (r + 1) → Ω) {j : Fin (r + 1)} (hj : h j ≠ 0) {a : Ω}
    (ha : a ∈ ampleBase (S := k) h j) : a ∈ funField (k := k) h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleDim».«ampleBase_le_funField» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDim_ampleBase_le_funField_3c18574d4cd9
