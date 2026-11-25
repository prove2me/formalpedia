-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_genDegAt_zero_e0e6f6c5241e
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_genDegAt_zero_e0e6f6c5241e
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:46:55.492284+00:00
-- url     : https://prove2.me/theorems/c0dddc5a-15f2-5a15-ab6e-991df86562e9
-- title:
--   P2 M Ground Theory Heights  Heights Inter Pushforward Arith Intersection gen Deg At zero e0e6f6c5241e: P2 M Ground Theory Heights  Heights Inter Pushforward Arith Intersection gen Deg At zero e0e6f6c5
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Pushforward Arith Intersection gen Deg At zero e0e6f6c5241e construction uses the P2 M Ground Theory Heights  Heights Inter Pushforward Arith Intersection gen Deg At zero e0e6f6c5241e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsMultiHomogRenameCoordPow.lean#L110-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsMultiHomogRenameCoordPow.lean#L110-L112

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsFieldIntersectionNoBlockFam
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogRenameCoordPow
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter.PushforwardArithIntersection
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_genDegAt_zero_e0e6f6c5241e (h0 : ArithVarZeroStatement) (I : AllFam) : GenDegAt I 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PushforwardArithIntersection».«genDegAt_zero» := P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_genDegAt_zero_e0e6f6c5241e
