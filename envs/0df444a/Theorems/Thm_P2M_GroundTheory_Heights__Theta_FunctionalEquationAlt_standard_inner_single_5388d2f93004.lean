-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_standard_inner_single_5388d2f93004
-- name    : P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_standard_inner_single_5388d2f93004
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:42:44.838655+00:00
-- url     : https://prove2.me/theorems/ec502bd5-1ca7-5974-a768-918672b8f5bb
-- title:
--   P2 M Ground Theory Heights  Theta Functional Equation Alt standard inner single 5388d2f93004: P2 M Ground Theory Heights  Theta Functional Equation Alt standard inner single 5388d2f93004
-- statement:
--   The P2 M Ground Theory Heights  Theta Functional Equation Alt standard inner single 5388d2f93004 construction uses the P2 M Ground Theory Heights  Theta Functional Equation Alt standard inner single 5388d2f93004 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/MemRangeIffIsIntegral.lean#L462-L468
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/MemRangeIffIsIntegral.lean#L462-L468

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
variable (E) (n : ℕ)
variable {E n}
variable (E n)
variable {E n}

theorem P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_standard_inner_single_5388d2f93004 (τ : InfinitePlace E) (i : Fin n) :
    inner ℂ ((MetSpace.standard E n).pt τ (Pi.single i 1))
      ((MetSpace.standard E n).pt τ (Pi.single i 1)) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FunctionalEquationAlt».«standard_inner_single» := P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_standard_inner_single_5388d2f93004
