-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_piece_eq_zero_e4c34e9ca0e7
-- name    : P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_piece_eq_zero_e4c34e9ca0e7
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:19:05.794712+00:00
-- url     : https://prove2.me/theorems/41ee7f31-c90d-4e43-90e8-021ba38d4b8b
-- title:
--   P2 M Ground Theory Heights  Heights Four B Compact Support Stokes piece eq zero e4c34e9ca0e7: P2 M Ground Theory Heights  Heights Four B Compact Support Stokes piece eq zero e4c34e9ca0e7
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Compact Support Stokes piece eq zero e4c34e9ca0e7 construction uses the P2 M Ground Theory Heights  Heights Four B Compact Support Stokes piece eq zero e4c34e9ca0e7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/CompactSupportStokes.lean#L168-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/CompactSupportStokes.lean#L168-L237

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

theorem P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_piece_eq_zero_e4c34e9ca0e7 [T2Space X] (A : FinHolAtlas (e + 1) X) (χ : ChartPartition A)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (j : Fin A.n) (G : Set X)
    (hGo : IsOpen G) (hG : G ⊆ (A.chart j).source) (x0 : Fin e → X)
    (hGU : ∀ i, G ⊆ (Φ i).U (x0 i)) (w : X → ℝ) (hw : A.Smooth w)
    (hwc : IsCompact (tsupport w)) (hwG : tsupport w ⊆ G) :
    integralWith A χ (Fin.cons (LocPot.ofFun w) Φ) (fun _ => 1) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«CompactSupportStokes».«piece_eq_zero» := P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_piece_eq_zero_e4c34e9ca0e7
