-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isDegZeroSmooth_const_9ac4e995dbbc
-- name    : P2M_GroundTheory_Heights__Heights_isDegZeroSmooth_const_9ac4e995dbbc
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:47:23.614484+00:00
-- url     : https://prove2.me/theorems/953ed27d-82f3-4b6d-bea2-f6d741746f93
-- title:
--   P2 M Ground Theory Heights  Heights is Deg Zero Smooth const 9ac4e995dbbc: P2 M Ground Theory Heights  Heights is Deg Zero Smooth const 9ac4e995dbbc
-- statement:
--   The P2 M Ground Theory Heights  Heights is Deg Zero Smooth const 9ac4e995dbbc construction uses the P2 M Ground Theory Heights  Heights is Deg Zero Smooth const 9ac4e995dbbc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StokesObjects.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StokesObjects.lean#L26-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StokesObjects
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
open ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_isDegZeroSmooth_const_9ac4e995dbbc (a : ℝ) : IsDegZeroSmooth (ι := ι) (fun _ => a) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isDegZeroSmooth_const» := P2M_GroundTheory_Heights__Heights_isDegZeroSmooth_const_9ac4e995dbbc
