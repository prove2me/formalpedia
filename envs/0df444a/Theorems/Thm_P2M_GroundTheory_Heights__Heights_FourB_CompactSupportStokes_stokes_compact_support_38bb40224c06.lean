-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_stokes_compact_support_38bb40224c06
-- name    : P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_stokes_compact_support_38bb40224c06
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:17:41.103936+00:00
-- url     : https://prove2.me/theorems/da32b8c0-faf1-4483-b4d0-291617f118a3
-- title:
--   P2 M Ground Theory Heights  Heights Four B Compact Support Stokes stokes compact support 38bb40224c06: P2 M Ground Theory Heights  Heights Four B Compact Support Stokes stokes compact support 38bb4022
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Compact Support Stokes stokes compact support 38bb40224c06 construction uses the P2 M Ground Theory Heights  Heights Four B Compact Support Stokes stokes compact support 38bb40224c06 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/CompactSupportStokes.lean#L328-L341
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/CompactSupportStokes.lean#L328-L341

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

theorem P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_stokes_compact_support_38bb40224c06 [T2Space X] (A : FinHolAtlas (e + 1) X) (χ : ChartPartition A)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (w : X → ℝ) (hw : A.Smooth w)
    (hwc : HasCompactSupport w) :
    integralWith A χ (Fin.cons (LocPot.ofFun w) Φ) (fun _ => 1) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«CompactSupportStokes».«stokes_compact_support» := P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_stokes_compact_support_38bb40224c06
