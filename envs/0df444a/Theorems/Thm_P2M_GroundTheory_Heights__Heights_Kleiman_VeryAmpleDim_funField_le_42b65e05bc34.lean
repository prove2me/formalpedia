-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDim_funField_le_42b65e05bc34
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDim_funField_le_42b65e05bc34
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:59:31.309005+00:00
-- url     : https://prove2.me/theorems/209a1a4e-f104-565b-af98-c7a66d5ab6fc
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample Dim fun Field le 42b65e05bc34: P2 M Ground Theory Heights  Heights Kleiman Very Ample Dim fun Field le 42b65e05bc34
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample Dim fun Field le 42b65e05bc34 construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample Dim fun Field le 42b65e05bc34 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleDim.lean#L35-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleDim.lean#L35-L59

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDim_funField_le_42b65e05bc34 (Nb : LineBundle k x) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hv : IsVeryAmpleBy Nb.toSubSystem h) {i : Fin (N + 1)} (hi : x i ≠ 0) :
    funField (k := k) h ≤ funField (k := k) x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleDim».«funField_le» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDim_funField_le_42b65e05bc34
