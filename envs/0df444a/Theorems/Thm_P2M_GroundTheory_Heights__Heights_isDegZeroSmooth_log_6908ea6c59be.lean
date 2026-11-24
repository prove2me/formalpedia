-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isDegZeroSmooth_log_6908ea6c59be
-- name    : P2M_GroundTheory_Heights__Heights_isDegZeroSmooth_log_6908ea6c59be
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:47.174912+00:00
-- url     : https://prove2.me/theorems/5a7b1a90-121d-490e-aadd-b318dc836ccb
-- title:
--   P2 M Ground Theory Heights  Heights is Deg Zero Smooth log 6908ea6c59be: P2 M Ground Theory Heights  Heights is Deg Zero Smooth log 6908ea6c59be
-- statement:
--   The P2 M Ground Theory Heights  Heights is Deg Zero Smooth log 6908ea6c59be construction uses the P2 M Ground Theory Heights  Heights is Deg Zero Smooth log 6908ea6c59be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StokesObjects.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StokesObjects.lean#L21-L24

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

theorem P2M_GroundTheory_Heights__Heights_isDegZeroSmooth_log_6908ea6c59be {B : HermLine ι} (hB : IsSmoothHerm B) (h0 : B.a = 0) :
    IsDegZeroSmooth (fun z => Real.log (B.h z)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isDegZeroSmooth_log» := P2M_GroundTheory_Heights__Heights_isDegZeroSmooth_log_6908ea6c59be
