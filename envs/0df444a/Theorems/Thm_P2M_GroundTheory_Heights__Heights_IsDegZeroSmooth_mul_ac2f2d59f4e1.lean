-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsDegZeroSmooth_mul_ac2f2d59f4e1
-- name    : P2M_GroundTheory_Heights__Heights_IsDegZeroSmooth_mul_ac2f2d59f4e1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:42.370308+00:00
-- url     : https://prove2.me/theorems/01eee7d8-d2ec-4b09-adca-075f1f2e3481
-- title:
--   P2 M Ground Theory Heights  Heights Is Deg Zero Smooth mul ac2f2d59f4e1: P2 M Ground Theory Heights  Heights Is Deg Zero Smooth mul ac2f2d59f4e1
-- statement:
--   The P2 M Ground Theory Heights  Heights Is Deg Zero Smooth mul ac2f2d59f4e1 construction uses the P2 M Ground Theory Heights  Heights Is Deg Zero Smooth mul ac2f2d59f4e1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StokesObjects.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StokesObjects.lean#L29-L31

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

theorem P2M_GroundTheory_Heights__Heights_IsDegZeroSmooth_mul_ac2f2d59f4e1 {u v : ((Σ k, ι k) → ℂ) → ℝ} (hu : IsDegZeroSmooth u)
    (hv : IsDegZeroSmooth v) : IsDegZeroSmooth (fun z => u z * v z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IsDegZeroSmooth».«mul» := P2M_GroundTheory_Heights__Heights_IsDegZeroSmooth_mul_ac2f2d59f4e1
