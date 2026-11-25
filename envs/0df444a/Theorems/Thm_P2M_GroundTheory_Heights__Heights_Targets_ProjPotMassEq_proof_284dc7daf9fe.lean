-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_proof_284dc7daf9fe
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_proof_284dc7daf9fe
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:47:21.167901+00:00
-- url     : https://prove2.me/theorems/1b711e9b-5e7e-5c84-a870-b89ef3febb53
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq proof 284dc7daf9fe: P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq proof 284dc7daf9fe
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq proof 284dc7daf9fe construction uses the P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq proof 284dc7daf9fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotMassEq.lean#L106-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotMassEq.lean#L106-L115

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotMassEqGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotMassEq
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_proof_85eb971859f8

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

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_proof_284dc7daf9fe : ProjPotMassEq.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjPotMassEq».«proof» := P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_proof_284dc7daf9fe
