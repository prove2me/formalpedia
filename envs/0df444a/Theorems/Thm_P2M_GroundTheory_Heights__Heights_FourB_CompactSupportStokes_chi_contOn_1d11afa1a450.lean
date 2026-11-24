-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_chi_contOn_1d11afa1a450
-- name    : P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_chi_contOn_1d11afa1a450
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:03:15.413746+00:00
-- url     : https://prove2.me/theorems/f00a22ff-370d-4264-92cf-9133b27239ec
-- title:
--   P2 M Ground Theory Heights  Heights Four B Compact Support Stokes chi cont On 1d11afa1a450: P2 M Ground Theory Heights  Heights Four B Compact Support Stokes chi cont On 1d11afa1a450
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Compact Support Stokes chi cont On 1d11afa1a450 construction uses the P2 M Ground Theory Heights  Heights Four B Compact Support Stokes chi cont On 1d11afa1a450 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/CompactSupportStokes.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/CompactSupportStokes.lean#L14-L17

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_CompactSupportStokes
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB GroundTheory.Heights₂.Heights.FourB.CompactSupportStokes
open MeasureTheory Filter Topology Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M FinHolAtlas
open scoped ContDiff Manifold
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_chi_contOn_1d11afa1a450 (A : FinHolAtlas e X) (χ : ChartPartition A) (k j : Fin A.n) :
    ContinuousOn (fun y => χ.χ k ((A.chart j).symm y)) (A.chart j).target := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«CompactSupportStokes».«chi_contOn» := P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_chi_contOn_1d11afa1a450
