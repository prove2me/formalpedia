-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_sgn_insert_925364762348
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_sgn_insert_925364762348
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:59.173665+00:00
-- url     : https://prove2.me/theorems/58ab1e4d-1734-48fd-855b-6926bddfe7c1
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Cone sgn insert 925364762348: P2 M Ground Theory Heights  Heights Kleiman Cech Cone sgn insert 925364762348
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Cone sgn insert 925364762348 construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Cone sgn insert 925364762348 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechCone.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechCone.lean#L18-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechCone
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
noncomputable section
universe u v
open GroundTheory.Heights₂.Heights.Kleiman.Cech GroundTheory.Heights₂.Heights.Kleiman.Cech.Cone
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_sgn_insert_925364762348 {a b : Fin n} {A : Finset (Fin n)} (ha : a ∉ A) :
    Cech.sgn (insert a A) b = Cech.sgn A b * (if a < b then -1 else 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Cech».«Cone».«sgn_insert» := P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_sgn_insert_925364762348
