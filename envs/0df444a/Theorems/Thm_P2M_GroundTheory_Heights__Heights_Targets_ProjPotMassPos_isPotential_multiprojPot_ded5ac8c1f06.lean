-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassPos_isPotential_multiprojPot_ded5ac8c1f06
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassPos_isPotential_multiprojPot_ded5ac8c1f06
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:55:31.480623+00:00
-- url     : https://prove2.me/theorems/10885bd4-2a64-51c0-b106-9746aad5f2c5
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Pos is Potential multiproj Pot ded5ac8c1f06: P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Pos is Potential multiproj Pot ded5ac8c
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Pos is Potential multiproj Pot ded5ac8c1f06 construction uses the P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Pos is Potential multiproj Pot ded5ac8c1f06 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotMassPos.lean#L35-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotMassPos.lean#L35-L55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotMassPos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveDegreeVert
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotMassPos
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

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassPos_isPotential_multiprojPot_ded5ac8c1f06 {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {n : ℕ} {R : AnLogRes P J (n + 1)} {V : Set R.X}
    {BV : FinHolAtlas n V} (hH : HoloMap BV R.A Subtype.val) :
    IsPotential BV (multiprojPot R V) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjPotMassPos».«isPotential_multiprojPot» := P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassPos_isPotential_multiprojPot_ded5ac8c1f06
