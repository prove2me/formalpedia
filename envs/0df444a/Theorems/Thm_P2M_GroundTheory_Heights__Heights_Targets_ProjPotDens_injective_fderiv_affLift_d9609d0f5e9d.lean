-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_injective_fderiv_affLift_d9609d0f5e9d
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_injective_fderiv_affLift_d9609d0f5e9d
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:50:58.562394+00:00
-- url     : https://prove2.me/theorems/3312c6dd-ba9f-59e8-a10e-49ebeb230f44
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Pot Dens injective fderiv aff Lift d9609d0f5e9d: P2 M Ground Theory Heights  Heights Targets Proj Pot Dens injective fderiv aff Lift d9609d0f5e9d
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Pot Dens injective fderiv aff Lift d9609d0f5e9d construction uses the P2 M Ground Theory Heights  Heights Targets Proj Pot Dens injective fderiv aff Lift d9609d0f5e9d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotDens.lean#L53-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotDens.lean#L53-L108

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotDensLevi
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotDens
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
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology
open GroundTheory.Heights₂.Heights.Targets.ProjPotDens
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {n : ℕ} {R : AnLogRes P J (n + 1)} {V : Set R.X} {BV : FinHolAtlas n V}

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_injective_fderiv_affLift_d9609d0f5e9d (hB : HoloMap BV R.A Subtype.val) (x : V) (p : (k : K) → ι k)
    (hp : ∀ k, R.lift x.1 x.1 ⟨k, p k⟩ ≠ 0) {j j' : Fin BV.n} (hj : x ∈ (BV.chart j).source)
    (hj' : x ∈ (BV.chart j').source)
    (hr : Module.finrank ℂ (LinearMap.range (fderiv ℂ
      (fun u => affCoord p (R.lift x.1 ((BV.chart j').symm u).1)) (BV.chart j' x) :
        (Fin n → ℂ) →ₗ[ℂ] ((Σ k, ι k) → ℂ))) = n) :
    Function.Injective (fderiv ℂ (fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1))
      (BV.chart j x)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjPotDens».«injective_fderiv_affLift» := P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_injective_fderiv_affLift_d9609d0f5e9d
