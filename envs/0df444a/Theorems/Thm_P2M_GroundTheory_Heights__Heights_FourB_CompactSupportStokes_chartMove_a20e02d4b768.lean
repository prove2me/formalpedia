-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_chartMove_a20e02d4b768
-- name    : P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_chartMove_a20e02d4b768
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:18:32.872025+00:00
-- url     : https://prove2.me/theorems/362d8369-df8b-4491-adc8-0a8a5b133e7c
-- title:
--   P2 M Ground Theory Heights  Heights Four B Compact Support Stokes chart Move a20e02d4b768: P2 M Ground Theory Heights  Heights Four B Compact Support Stokes chart Move a20e02d4b768
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Compact Support Stokes chart Move a20e02d4b768 construction uses the P2 M Ground Theory Heights  Heights Four B Compact Support Stokes chart Move a20e02d4b768 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/CompactSupportStokes.lean#L38-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/CompactSupportStokes.lean#L38-L86

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

theorem P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_chartMove_a20e02d4b768 (A : FinHolAtlas e X) (χ : ChartPartition A) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (j k : Fin A.n) (g : X → ℝ)
    (hs : ∀ y ∈ (A.chart k).target, (A.chart k).symm y ∉ (A.chart j).source →
      g ((A.chart k).symm y) * locDens A Φ k y = 0) :
    ∫ y in (A.chart k).target,
        χ.χ k ((A.chart k).symm y) * g ((A.chart k).symm y) * locDens A Φ k y =
      ∫ y in (A.chart j).target,
        χ.χ k ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«CompactSupportStokes».«chartMove» := P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_chartMove_a20e02d4b768
