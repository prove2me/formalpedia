-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_not_isField_stalk_of_ne_genericPoint_1cad4102bfa7
-- name    : P2M_GroundTheory_Heights__Heights_Model_not_isField_stalk_of_ne_genericPoint_1cad4102bfa7
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:29:36.382496+00:00
-- url     : https://prove2.me/theorems/b47aa22b-27ac-4dce-9ce6-da8ae812645d
-- title:
--   P2 M Ground Theory Heights  Heights Model not is Field stalk of ne generic Point 1cad4102bfa7: P2 M Ground Theory Heights  Heights Model not is Field stalk of ne generic Point 1cad4102bfa7
-- statement:
--   The P2 M Ground Theory Heights  Heights Model not is Field stalk of ne generic Point 1cad4102bfa7 construction uses the P2 M Ground Theory Heights  Heights Model not is Field stalk of ne generic Point 1cad4102bfa7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PDominatingDVRScheme.lean#L19-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PDominatingDVRScheme.lean#L19-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PDominatingDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PKrullAkizuki
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PKrullAkizukiQuotientLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PTorsionFreeQuotientLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PBlowUpChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PDominatingDVRScheme
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open AlgebraicGeometry

theorem P2M_GroundTheory_Heights__Heights_Model_not_isField_stalk_of_ne_genericPoint_1cad4102bfa7 (Z : Scheme.{0}) [IsIntegral Z] (z : Z)
    (hz : z ≠ genericPoint Z) : ¬ IsField (Z.presheaf.stalk z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«not_isField_stalk_of_ne_genericPoint» := P2M_GroundTheory_Heights__Heights_Model_not_isField_stalk_of_ne_genericPoint_1cad4102bfa7
