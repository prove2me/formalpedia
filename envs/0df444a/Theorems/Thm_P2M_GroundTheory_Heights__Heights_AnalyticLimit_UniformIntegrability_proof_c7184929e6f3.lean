-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_UniformIntegrability_proof_c7184929e6f3
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_UniformIntegrability_proof_c7184929e6f3
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:46:47.486331+00:00
-- url     : https://prove2.me/theorems/70f991b6-c531-5f4b-a321-502cd14ab0f7
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit Uniform Integrability proof c7184929e6f3: P2 M Ground Theory Heights  Heights Analytic Limit Uniform Integrability proof c7184929e6f3
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit Uniform Integrability proof c7184929e6f3 construction uses the P2 M Ground Theory Heights  Heights Analytic Limit Uniform Integrability proof c7184929e6f3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/UniformIntegrability.lean#L19-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/UniformIntegrability.lean#L19-L69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_GreenMassZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_GreenMassStep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_GreenMassReplace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_GreenMassError
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_UniformIntegrability
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open ReciprocityTheory.AnForm.M (mInt)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_UniformIntegrability_proof_c7184929e6f3 (h₀ : GreenMassZero.Statement) (h₁ : GreenMassStep.Statement)
    (h₂ : GreenMassReplace.Statement) (h₃ : GreenMassError.Statement) :
    UniformIntegrability.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«UniformIntegrability».«proof» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_UniformIntegrability_proof_c7184929e6f3
