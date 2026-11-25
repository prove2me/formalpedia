-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_integrableOn_target_0b55a0c19207
-- name    : P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_integrableOn_target_0b55a0c19207
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:19:06.046374+00:00
-- url     : https://prove2.me/theorems/40559019-1371-4900-81c2-1d87c0a74a0e
-- title:
--   P2 M Ground Theory Heights  Heights Four B Compact Support Stokes integrable On target 0b55a0c19207: P2 M Ground Theory Heights  Heights Four B Compact Support Stokes integrable On target 0b55a0c19207
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Compact Support Stokes integrable On target 0b55a0c19207 construction uses the P2 M Ground Theory Heights  Heights Four B Compact Support Stokes integrable On target 0b55a0c19207 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/CompactSupportStokes.lean#L19-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/CompactSupportStokes.lean#L19-L31

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

theorem P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_integrableOn_target_0b55a0c19207 (A : FinHolAtlas e X) (k : Fin A.n) {F : (Fin e → ℂ) → ℝ}
    (hF : ContinuousOn F (A.chart k).target) {S : Set X} (hS : IsCompact S)
    (hSk : S ⊆ (A.chart k).source)
    (hz : ∀ y ∈ (A.chart k).target, (A.chart k).symm y ∉ S → F y = 0) :
    IntegrableOn F (A.chart k).target := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«CompactSupportStokes».«integrableOn_target» := P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_integrableOn_target_0b55a0c19207
