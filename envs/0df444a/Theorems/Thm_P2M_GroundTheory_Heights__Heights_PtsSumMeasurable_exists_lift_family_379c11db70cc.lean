-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSumMeasurable_exists_lift_family_379c11db70cc
-- name    : P2M_GroundTheory_Heights__Heights_PtsSumMeasurable_exists_lift_family_379c11db70cc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:02.800881+00:00
-- url     : https://prove2.me/theorems/d8ddbadf-d54f-438e-8edd-28e869c963c5
-- title:
--   P2 M Ground Theory Heights  Heights Pts Sum Measurable exists lift family 379c11db70cc: P2 M Ground Theory Heights  Heights Pts Sum Measurable exists lift family 379c11db70cc
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Sum Measurable exists lift family 379c11db70cc construction uses the P2 M Ground Theory Heights  Heights Pts Sum Measurable exists lift family 379c11db70cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PtsSumMeasurableA.lean#L36-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PtsSumMeasurableA.lean#L36-L113

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsSumMeasurableA
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
open MeasureTheory Metric Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.PtsSumMeasurable
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_PtsSumMeasurable_exists_lift_family_379c11db70cc {P : Ideal (MRing ι)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hfin : ∀ y, (fibre P Ψ y).Finite) :
    ∃ (B : ℕ → Set (Fin e → ℂ)) (γ : ℕ → (Fin e → ℂ) → (Σ k, ι k) → ℂ),
      (∀ m, IsOpen (B m)) ∧
      (∀ m, ∀ y ∈ B m, DifferentiableAt ℂ (γ m) y ∧ γ m y ∈ mcPts P ∧
        Ψ (segre (γ m y)) = Fin.cons 1 y) ∧
      ∀ y w γ', IsSheet P Ψ y w γ' → ∃ m, y ∈ B m ∧ segre (γ m y) = w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsSumMeasurable».«exists_lift_family» := P2M_GroundTheory_Heights__Heights_PtsSumMeasurable_exists_lift_family_379c11db70cc
