-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_dualHom_f34f43fa1a82
-- name    : P2M_GroundTheory_Heights__Theta_UnitaryReduction_dualHom_f34f43fa1a82
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:47:06.625023+00:00
-- url     : https://prove2.me/theorems/d5ae6727-5211-4fd8-8a95-a9b9571fea3c
-- title:
--   P2 M Ground Theory Heights  Theta Unitary Reduction dual Hom f34f43fa1a82: P2 M Ground Theory Heights  Theta Unitary Reduction dual Hom f34f43fa1a82
-- statement:
--   The P2 M Ground Theory Heights  Theta Unitary Reduction dual Hom f34f43fa1a82 construction uses the P2 M Ground Theory Heights  Theta Unitary Reduction dual Hom f34f43fa1a82 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L593-L754
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L593-L754

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_UnitaryReduction_UnipotentRadicalPlaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearFormEqZeroOfIntegers
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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.UnitaryReduction
open NumberField Module FunctionalEquationAlt FunctionalEquationAlt.MetSpace DualHomPf
open scoped InnerProductSpace nonZeroDivisors

theorem P2M_GroundTheory_Heights__Theta_UnitaryReduction_dualHom_f34f43fa1a82 (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
    [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E] :
    DualHom.Statement F E := by sorry

alias «GroundTheory».«Heights₂».«Theta».«UnitaryReduction».«dualHom» := P2M_GroundTheory_Heights__Theta_UnitaryReduction_dualHom_f34f43fa1a82
