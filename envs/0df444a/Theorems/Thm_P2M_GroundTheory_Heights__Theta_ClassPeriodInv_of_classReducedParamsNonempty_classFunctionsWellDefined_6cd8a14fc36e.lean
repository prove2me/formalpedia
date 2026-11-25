-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_ClassPeriodInv_of_classReducedParamsNonempty_classFunctionsWellDefined_6cd8a14fc36e
-- name    : P2M_GroundTheory_Heights__Theta_ClassPeriodInv_of_classReducedParamsNonempty_classFunctionsWellDefined_6cd8a14fc36e
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:42:16.535579+00:00
-- url     : https://prove2.me/theorems/678112ea-df94-4aa0-96ea-dd2085ba1c21
-- title:
--   P2 M Ground Theory Heights  Theta Class Period Inv of class Reduced Params Nonempty class Functions Well Defined 6cd8a14fc36e: P2 M Ground Theory Heights  Theta Class Period Inv of class Reduced Param
-- statement:
--   The P2 M Ground Theory Heights  Theta Class Period Inv of class Reduced Params Nonempty class Functions Well Defined 6cd8a14fc36e construction uses the P2 M Ground Theory Heights  Theta Class Period Inv of class Reduced Params Nonempty class Functions Well Defined 6cd8a14fc36e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassPeriodInvConj.lean#L259-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassPeriodInvConj.lean#L259-L268

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaLogPeriodNegConjPf
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmClassPeriodInvConj
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
open UpperHalfPlane ModularGroup ModularForm Complex NumberField Module
open scoped Real Modular MatrixGroups nonZeroDivisors
open GroundTheory.Heights₂.Theta.ClassPeriodInv
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Theta_ClassPeriodInv_of_classReducedParamsNonempty_classFunctionsWellDefined_6cd8a14fc36e
    (hne : ClassReducedParamsNonempty.Statement) (hwd : ClassFunctionsWellDefined.Statement) :
    ClassPeriodInv.Statement := by sorry

alias «GroundTheory».«Heights₂».«Theta».«ClassPeriodInv».«of_classReducedParamsNonempty_classFunctionsWellDefined» := P2M_GroundTheory_Heights__Theta_ClassPeriodInv_of_classReducedParamsNonempty_classFunctionsWellDefined_6cd8a14fc36e
