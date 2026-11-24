-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_sgn_mul_self_b354143a435a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_sgn_mul_self_b354143a435a
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:57.823456+00:00
-- url     : https://prove2.me/theorems/afc651cd-7530-48ad-89d4-0839776ba900
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Cone sgn mul self b354143a435a: P2 M Ground Theory Heights  Heights Kleiman Cech Cone sgn mul self b354143a435a
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Cone sgn mul self b354143a435a construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Cone sgn mul self b354143a435a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechCone.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechCone.lean#L26-L28

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_sgn_mul_self_b354143a435a (A : Finset (Fin n)) (b : Fin n) : Cech.sgn A b * Cech.sgn A b = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Cech».«Cone».«sgn_mul_self» := P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_sgn_mul_self_b354143a435a
