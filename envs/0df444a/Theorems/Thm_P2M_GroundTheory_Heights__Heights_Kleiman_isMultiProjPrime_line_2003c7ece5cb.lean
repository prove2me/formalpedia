-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_isMultiProjPrime_line_2003c7ece5cb
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_isMultiProjPrime_line_2003c7ece5cb
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:31:43.219659+00:00
-- url     : https://prove2.me/theorems/a9a2ba72-156f-5d62-86ab-ad765bce6026
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman is Multi Proj Prime line 2003c7ece5cb: P2 M Ground Theory Heights  Heights Kleiman is Multi Proj Prime line 2003c7ece5cb
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman is Multi Proj Prime line 2003c7ece5cb construction uses the P2 M Ground Theory Heights  Heights Kleiman is Multi Proj Prime line 2003c7ece5cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/Objects.lean#L929-L931
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/Objects.lean#L929-L931

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
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
open MvPolynomial
noncomputable section
universe u v w
variable (k : Type u) [Field k]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_isMultiProjPrime_line_2003c7ece5cb :
    NumbersDVR.IsMultiProjPrime (primeOfOne (S := k) (lineX k)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«isMultiProjPrime_line» := P2M_GroundTheory_Heights__Heights_Kleiman_isMultiProjPrime_line_2003c7ece5cb
