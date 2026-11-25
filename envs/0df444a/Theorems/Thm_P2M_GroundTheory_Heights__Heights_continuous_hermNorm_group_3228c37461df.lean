-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_continuous_hermNorm_group_3228c37461df
-- name    : P2M_GroundTheory_Heights__Heights_continuous_hermNorm_group_3228c37461df
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:45:26.754802+00:00
-- url     : https://prove2.me/theorems/1eb6ac3e-411d-47ef-97f2-6f25358d2223
-- title:
--   P2 M Ground Theory Heights  Heights continuous herm Norm group 3228c37461df: P2 M Ground Theory Heights  Heights continuous herm Norm group 3228c37461df
-- statement:
--   The P2 M Ground Theory Heights  Heights continuous herm Norm group 3228c37461df construction uses the P2 M Ground Theory Heights  Heights continuous herm Norm group 3228c37461df property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ContinuousHermNormGroup.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ContinuousHermNormGroup.lean#L25-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory NumberField
noncomputable section
open Matrix
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_continuous_hermNorm_group_3228c37461df (h : HermNorm n) {k : ℕ} (i : Fin k) :
    Continuous fun u : Fin k × Fin n → ℂ => h.norm (fun j => u (i, j)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«continuous_hermNorm_group» := P2M_GroundTheory_Heights__Heights_continuous_hermNorm_group_3228c37461df
