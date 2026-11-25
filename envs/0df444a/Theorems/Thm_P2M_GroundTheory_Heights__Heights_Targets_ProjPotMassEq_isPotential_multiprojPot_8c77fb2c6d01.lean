-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_isPotential_multiprojPot_8c77fb2c6d01
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_isPotential_multiprojPot_8c77fb2c6d01
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:46:47.454471+00:00
-- url     : https://prove2.me/theorems/c2b54763-ed45-5d45-a7fc-5c05116bca2d
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq is Potential multiproj Pot 8c77fb2c6d01: P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq is Potential multiproj Pot 8c77fb2c6d
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq is Potential multiproj Pot 8c77fb2c6d01 construction uses the P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq is Potential multiproj Pot 8c77fb2c6d01 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotMassEq.lean#L65-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotMassEq.lean#L65-L75

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotMassEqGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotMassEq
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
open scoped ContDiff
open GroundTheory.Heights₂.Heights.Targets.ProjPotMassEq
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {n : ℕ} {R : AnLogRes P J (n + 1)}

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_isPotential_multiprojPot_8c77fb2c6d01 {V : Set R.X} {BV : FinHolAtlas n V}
    (hH : HoloMap BV R.A Subtype.val) : IsPotential BV (multiprojPot R V) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjPotMassEq».«isPotential_multiprojPot» := P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_isPotential_multiprojPot_8c77fb2c6d01
