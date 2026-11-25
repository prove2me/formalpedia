-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_invol_of_quadratic_a0cb9d4cbe1b
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_invol_of_quadratic_a0cb9d4cbe1b
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:40:35.387803+00:00
-- url     : https://prove2.me/theorems/cb893aea-242f-584a-8667-fbf8ccb8de15
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx invol of quadratic a0cb9d4cbe1b: P2 M Ground Theory Heights  Heights Strong Approx invol of quadratic a0cb9d4cbe1b
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx invol of quadratic a0cb9d4cbe1b construction uses the P2 M Ground Theory Heights  Heights Strong Approx invol of quadratic a0cb9d4cbe1b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PClosureIsSubmonoid.lean#L13-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PClosureIsSubmonoid.lean#L13-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PClosureIsSubmonoid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_invol_of_quadratic_a0cb9d4cbe1b {F E : Type} [Field F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E)
    (h2 : Module.finrank F E = 2) (hc : c ≠ 1) (x : E) : c (c x) = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«invol_of_quadratic» := P2M_GroundTheory_Heights__Heights_StrongApprox_invol_of_quadratic_a0cb9d4cbe1b
