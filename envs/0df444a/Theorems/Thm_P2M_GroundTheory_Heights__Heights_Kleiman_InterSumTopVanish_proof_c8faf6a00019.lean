-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_InterSumTopVanish_proof_c8faf6a00019
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_InterSumTopVanish_proof_c8faf6a00019
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:31:56.396796+00:00
-- url     : https://prove2.me/theorems/050b138c-6cc0-40ed-a611-7de550d196ec
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Inter Sum Top Vanish proof c8faf6a00019: P2 M Ground Theory Heights  Heights Kleiman Inter Sum Top Vanish proof c8faf6a00019
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Inter Sum Top Vanish proof c8faf6a00019 construction uses the P2 M Ground Theory Heights  Heights Kleiman Inter Sum Top Vanish proof c8faf6a00019 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterSumTopVanish.lean#L17-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterSumTopVanish.lean#L17-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterSumTopVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StMixedTwistShift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PInterNumAdditive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PInterSumTopVanish
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GenericPointSectionInput_proof_e6d51449fcf0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_InterNumAdditive_proof_a78390f278f3

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
open MvPolynomial Filter
noncomputable section
universe u w
attribute [local instance] twistMonoid

theorem P2M_GroundTheory_Heights__Heights_Kleiman_InterSumTopVanish_proof_c8faf6a00019 (hM : MixedTwistShift.Statement.{u, w}) : InterSumTopVanish.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«InterSumTopVanish».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_InterSumTopVanish_proof_c8faf6a00019
