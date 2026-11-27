-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_hypForm_isotropic_27d4a9171a2f
-- name    : P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_hypForm_isotropic_27d4a9171a2f
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:42:47.878811+00:00
-- url     : https://prove2.me/theorems/068c206b-b9dd-5f4f-9706-3464bd2dac6d
-- title:
--   P2 M Ground Theory Heights  Theta Functional Equation Alt hyp Form isotropic 27d4a9171a2f: P2 M Ground Theory Heights  Theta Functional Equation Alt hyp Form isotropic 27d4a9171a2f
-- statement:
--   The P2 M Ground Theory Heights  Theta Functional Equation Alt hyp Form isotropic 27d4a9171a2f construction uses the P2 M Ground Theory Heights  Theta Functional Equation Alt hyp Form isotropic 27d4a9171a2f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/MemRangeIffIsIntegral.lean#L611-L615
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/MemRangeIffIsIntegral.lean#L611-L615

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
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]
  [Algebra F E] [Algebra.IsQuadraticExtension F E]

theorem P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_hypForm_isotropic_27d4a9171a2f :
    (hypForm (F := F) (E := E)).toSesq ![1, 1] ![1, 1] = 0 ∧ (![1, 1] : Fin 2 → E) ∈ stdLat E 2 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FunctionalEquationAlt».«hypForm_isotropic» := P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_hypForm_isotropic_27d4a9171a2f
