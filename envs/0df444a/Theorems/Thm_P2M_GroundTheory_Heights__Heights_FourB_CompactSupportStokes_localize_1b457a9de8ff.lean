-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_localize_1b457a9de8ff
-- name    : P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_localize_1b457a9de8ff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:34:48.227273+00:00
-- url     : https://prove2.me/theorems/bb8e6211-bf0c-48a4-85da-384b31f612cb
-- title:
--   P2 M Ground Theory Heights  Heights Four B Compact Support Stokes localize 1b457a9de8ff: P2 M Ground Theory Heights  Heights Four B Compact Support Stokes localize 1b457a9de8ff
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Compact Support Stokes localize 1b457a9de8ff construction uses the P2 M Ground Theory Heights  Heights Four B Compact Support Stokes localize 1b457a9de8ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/CompactSupportStokes.lean#L88-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/CompactSupportStokes.lean#L88-L100

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

theorem P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_localize_1b457a9de8ff (A : FinHolAtlas e X) (χ : ChartPartition A) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (j : Fin A.n) (g : X → ℝ)
    (hs : ∀ k, ∀ y ∈ (A.chart k).target, (A.chart k).symm y ∉ (A.chart j).source →
      g ((A.chart k).symm y) * locDens A Φ k y = 0)
    (hint : ∀ k, IntegrableOn (fun y => χ.χ k ((A.chart j).symm y) * g ((A.chart j).symm y) *
      locDens A Φ j y) (A.chart j).target) :
    integralWith A χ Φ g =
      ∫ y in (A.chart j).target, g ((A.chart j).symm y) * locDens A Φ j y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«CompactSupportStokes».«localize» := P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_localize_1b457a9de8ff
