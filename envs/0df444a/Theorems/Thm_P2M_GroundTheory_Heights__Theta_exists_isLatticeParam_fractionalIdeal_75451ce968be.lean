-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_exists_isLatticeParam_fractionalIdeal_75451ce968be
-- name    : P2M_GroundTheory_Heights__Theta_exists_isLatticeParam_fractionalIdeal_75451ce968be
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:53:28.682321+00:00
-- url     : https://prove2.me/theorems/4302c512-43e4-51dc-a473-67ba9f066921
-- title:
--   P2 M Ground Theory Heights  Theta exists is Lattice Param fractional Ideal 75451ce968be: P2 M Ground Theory Heights  Theta exists is Lattice Param fractional Ideal 75451ce968be
-- statement:
--   The P2 M Ground Theory Heights  Theta exists is Lattice Param fractional Ideal 75451ce968be construction uses the P2 M Ground Theory Heights  Theta exists is Lattice Param fractional Ideal 75451ce968be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassReducedParamsNonemptyPf.lean#L113-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassReducedParamsNonemptyPf.lean#L113-L156

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmClassReducedParamsNonemptyPf
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open UpperHalfPlane ModularGroup Complex NumberField
open scoped Real MatrixGroups nonZeroDivisors
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Theta_exists_isLatticeParam_fractionalIdeal_75451ce968be (h2 : Module.finrank ℚ K = 2) (σ : K →+* ℂ)
    (hσ : ∃ x : K, (σ x).im ≠ 0) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ τ : ℍ, IsLatticeParam (σ '' ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K)) τ := by sorry

alias «GroundTheory».«Heights₂».«Theta».«exists_isLatticeParam_fractionalIdeal» := P2M_GroundTheory_Heights__Theta_exists_isLatticeParam_fractionalIdeal_75451ce968be
