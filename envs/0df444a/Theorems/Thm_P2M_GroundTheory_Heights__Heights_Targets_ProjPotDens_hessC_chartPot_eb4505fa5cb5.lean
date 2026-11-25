-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_hessC_chartPot_eb4505fa5cb5
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_hessC_chartPot_eb4505fa5cb5
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:06:56.405724+00:00
-- url     : https://prove2.me/theorems/61dba0ca-6351-463c-b0eb-4423558ac15d
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Pot Dens hess C chart Pot eb4505fa5cb5: P2 M Ground Theory Heights  Heights Targets Proj Pot Dens hess C chart Pot eb4505fa5cb5
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Pot Dens hess C chart Pot eb4505fa5cb5 construction uses the P2 M Ground Theory Heights  Heights Targets Proj Pot Dens hess C chart Pot eb4505fa5cb5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotDens.lean#L110-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotDens.lean#L110-L157

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

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_hessC_chartPot_eb4505fa5cb5 (hB : HoloMap BV R.A Subtype.val) (x : V) {j : Fin BV.n}
    (hx : x ∈ (BV.chart j).source) (p : (k : K) → ι k)
    (hp : ∀ k, R.lift x.1 x.1 ⟨k, p k⟩ ≠ 0) :
    ReciprocityTheory.AnForm.hessC (fun u => (multiprojPot R V).φ x ((BV.chart j).symm u)) (BV.chart j x) =
      ReciprocityTheory.AnForm.hessC
        (fsMultiPot ∘ fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1)) (BV.chart j x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjPotDens».«hessC_chartPot» := P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_hessC_chartPot_eb4505fa5cb5
