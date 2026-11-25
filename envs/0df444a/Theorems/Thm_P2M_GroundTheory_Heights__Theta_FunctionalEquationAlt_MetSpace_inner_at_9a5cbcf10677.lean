-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_MetSpace_inner_at_9a5cbcf10677
-- name    : P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_MetSpace_inner_at_9a5cbcf10677
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:42:46.995074+00:00
-- url     : https://prove2.me/theorems/de4ed03e-8276-5d7a-9315-29633c26eb1b
-- title:
--   P2 M Ground Theory Heights  Theta Functional Equation Alt Met Space inner at 9a5cbcf10677: P2 M Ground Theory Heights  Theta Functional Equation Alt Met Space inner at 9a5cbcf10677
-- statement:
--   The P2 M Ground Theory Heights  Theta Functional Equation Alt Met Space inner at 9a5cbcf10677 construction uses the P2 M Ground Theory Heights  Theta Functional Equation Alt Met Space inner at 9a5cbcf10677 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/MemRangeIffIsIntegral.lean#L115-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/MemRangeIffIsIntegral.lean#L115-L117

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianLattice
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_CMDatum
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_ChainWittIndexHypothesesMet
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_MemRangeIffIsIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.FunctionalEquationAlt
open NumberField TensorProduct Module GroundTheory.Automorphic
open scoped nonZeroDivisors
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open CAt
attribute [instance] MetSpace.instAddCommGroup MetSpace.instModule MetSpace.instFD
  MetSpace.instModuleO MetSpace.instTower
variable {E : Type} [Field E] [NumberField E]
open GroundTheory.Heights₂.Theta.FunctionalEquationAlt.MetSpace
variable (S : MetSpace E)

theorem P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_MetSpace_inner_at_9a5cbcf10677 (τ : InfinitePlace E) (v w : S.V) :
    inner ℂ (S.pt τ v) (S.pt τ w) =
      (S.form τ).inner ((1 : CAt τ.embedding) ⊗ₜ[E] v) ((1 : CAt τ.embedding) ⊗ₜ[E] w) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FunctionalEquationAlt».«MetSpace».«inner_at» := P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_MetSpace_inner_at_9a5cbcf10677
