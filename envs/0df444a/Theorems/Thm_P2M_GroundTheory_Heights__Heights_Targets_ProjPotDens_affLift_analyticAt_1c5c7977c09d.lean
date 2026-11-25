-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_affLift_analyticAt_1c5c7977c09d
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_affLift_analyticAt_1c5c7977c09d
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:03:56.469939+00:00
-- url     : https://prove2.me/theorems/a9b96976-af82-52b7-8e36-2f98ff0eb995
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Pot Dens aff Lift analytic At 1c5c7977c09d: P2 M Ground Theory Heights  Heights Targets Proj Pot Dens aff Lift analytic At 1c5c7977c09d
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Pot Dens aff Lift analytic At 1c5c7977c09d construction uses the P2 M Ground Theory Heights  Heights Targets Proj Pot Dens aff Lift analytic At 1c5c7977c09d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotDens.lean#L22-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotDens.lean#L22-L36

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

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_affLift_analyticAt_1c5c7977c09d (hB : HoloMap BV R.A Subtype.val) (x : V) {j : Fin BV.n}
    (hx : x ∈ (BV.chart j).source) (p : (k : K) → ι k)
    (hp : ∀ k, R.lift x.1 x.1 ⟨k, p k⟩ ≠ 0) :
    AnalyticAt ℂ (fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1)) (BV.chart j x) ∧
      ∀ᶠ u in 𝓝 (BV.chart j x), ∀ k, R.lift x.1 ((BV.chart j).symm u).1 ⟨k, p k⟩ ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjPotDens».«affLift_analyticAt» := P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_affLift_analyticAt_1c5c7977c09d
