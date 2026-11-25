-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_fderiv_affLift_self_42d939e87e9f
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_fderiv_affLift_self_42d939e87e9f
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:50:56.101298+00:00
-- url     : https://prove2.me/theorems/6c6b133a-2e22-5048-8a90-a34087b0e6d5
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Pot Dens fderiv aff Lift self 42d939e87e9f: P2 M Ground Theory Heights  Heights Targets Proj Pot Dens fderiv aff Lift self 42d939e87e9f
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Pot Dens fderiv aff Lift self 42d939e87e9f construction uses the P2 M Ground Theory Heights  Heights Targets Proj Pot Dens fderiv aff Lift self 42d939e87e9f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotDens.lean#L38-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotDens.lean#L38-L51

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

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_fderiv_affLift_self_42d939e87e9f (hB : HoloMap BV R.A Subtype.val) (x : V) {j : Fin BV.n}
    (hx : x ∈ (BV.chart j).source) (p : (k : K) → ι k)
    (hp : ∀ k, R.lift x.1 x.1 ⟨k, p k⟩ ≠ 0) (w : Fin n → ℂ) (k : K) :
    fderiv ℂ (fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1)) (BV.chart j x) w
      ⟨k, p k⟩ = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjPotDens».«fderiv_affLift_self» := P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_fderiv_affLift_self_42d939e87e9f
