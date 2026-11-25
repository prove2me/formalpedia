-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_CAt_algebraMap_apply_5dc063ae0e65
-- name    : P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_CAt_algebraMap_apply_5dc063ae0e65
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:45:45.22167+00:00
-- url     : https://prove2.me/theorems/8ff2636f-db29-44bf-93c2-7ae5d2250896
-- title:
--   P2 M Ground Theory Heights  Theta Functional Equation Alt CAt algebra Map apply 5dc063ae0e65: P2 M Ground Theory Heights  Theta Functional Equation Alt CAt algebra Map apply 5dc063ae0e65
-- statement:
--   The P2 M Ground Theory Heights  Theta Functional Equation Alt CAt algebra Map apply 5dc063ae0e65 construction uses the P2 M Ground Theory Heights  Theta Functional Equation Alt CAt algebra Map apply 5dc063ae0e65 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/MemRangeIffIsIntegral.lean#L35-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/MemRangeIffIsIntegral.lean#L35-L35

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianLattice
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_CMDatum
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_ChainWittIndexHypothesesMet
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_MemRangeIffIsIntegral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexAt_algebraMap_apply_de37bb391a59

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
open GroundTheory.Heights₂.Theta.FunctionalEquationAlt.CAt
variable {E : Type} [Field E] (σ : E →+* ℂ)

theorem P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_CAt_algebraMap_apply_5dc063ae0e65 (a : E) : algebraMap E (CAt σ) a = ofComplex σ (σ a) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FunctionalEquationAlt».«CAt».«algebraMap_apply» := P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_CAt_algebraMap_apply_5dc063ae0e65
