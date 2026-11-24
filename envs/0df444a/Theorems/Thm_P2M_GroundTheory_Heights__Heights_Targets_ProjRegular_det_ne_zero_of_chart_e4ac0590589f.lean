-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_det_ne_zero_of_chart_e4ac0590589f
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_det_ne_zero_of_chart_e4ac0590589f
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:57.045826+00:00
-- url     : https://prove2.me/theorems/d7d2d9ee-e601-4f10-b3be-434c4fe241ec
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Regular det ne zero of chart e4ac0590589f: P2 M Ground Theory Heights  Heights Targets Proj Regular det ne zero of chart e4ac0590589f
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Regular det ne zero of chart e4ac0590589f construction uses the P2 M Ground Theory Heights  Heights Targets Proj Regular det ne zero of chart e4ac0590589f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjRegular.lean#L96-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjRegular.lean#L96-L144

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeH
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
open GroundTheory.Heights₂.Heights.Targets.ProjRegular
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {n : ℕ} {R : AnLogRes P J (n + 1)} (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_det_ne_zero_of_chart_e4ac0590589f {V : Set R.X} {BV : FinHolAtlas n V}
    (hB : HoloMap BV R.A Subtype.val) (y : V) (h0 : Ψ (segre (R.lift y.1 y.1)) 0 ≠ 0)
    {j k : Fin BV.n} (hj : y ∈ (BV.chart j).source) (hk : y ∈ (BV.chart k).source)
    (hd : LinearMap.det (fderiv ℂ ((projCoord R Ψ ∘ Subtype.val) ∘ (BV.chart k).symm)
      (BV.chart k y) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0) :
    LinearMap.det (fderiv ℂ ((projCoord R Ψ ∘ Subtype.val) ∘ (BV.chart j).symm)
      (BV.chart j y) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjRegular».«det_ne_zero_of_chart» := P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_det_ne_zero_of_chart_e4ac0590589f
