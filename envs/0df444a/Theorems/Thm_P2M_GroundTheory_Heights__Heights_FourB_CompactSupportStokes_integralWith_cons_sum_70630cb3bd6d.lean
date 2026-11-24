-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_integralWith_cons_sum_70630cb3bd6d
-- name    : P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_integralWith_cons_sum_70630cb3bd6d
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:40.091787+00:00
-- url     : https://prove2.me/theorems/989e869b-fa75-4466-882a-ce0ec33525a0
-- title:
--   P2 M Ground Theory Heights  Heights Four B Compact Support Stokes integral With cons sum 70630cb3bd6d: P2 M Ground Theory Heights  Heights Four B Compact Support Stokes integral With cons sum 70630cb3
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Compact Support Stokes integral With cons sum 70630cb3bd6d construction uses the P2 M Ground Theory Heights  Heights Four B Compact Support Stokes integral With cons sum 70630cb3bd6d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/CompactSupportStokes.lean#L124-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/CompactSupportStokes.lean#L124-L166

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

theorem P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_integralWith_cons_sum_70630cb3bd6d [T2Space X] (A : FinHolAtlas (e + 1) X) (χ : ChartPartition A)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) {ι : Type*} (s : Finset ι)
    (f : ι → X → ℝ) (hf : ∀ m, A.Smooth (f m)) {L : Set X} (hL : IsCompact L)
    (hfL : ∀ m, tsupport (f m) ⊆ L) :
    integralWith A χ (Fin.cons (LocPot.ofFun fun x => ∑ m ∈ s, f m x) Φ) (fun _ => 1) =
      ∑ m ∈ s, integralWith A χ (Fin.cons (LocPot.ofFun (f m)) Φ) (fun _ => 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«CompactSupportStokes».«integralWith_cons_sum» := P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_integralWith_cons_sum_70630cb3bd6d
