-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_li_norm_nonneg_a218ca485846
-- name    : P2M_GroundTheory_Heights__Heights_HermNorm_li_norm_nonneg_a218ca485846
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:54:37.356374+00:00
-- url     : https://prove2.me/theorems/2f551400-89c9-43b5-bd74-e623e84ac537
-- title:
--   P2 M Ground Theory Heights  Heights Herm Norm li norm nonneg a218ca485846: P2 M Ground Theory Heights  Heights Herm Norm li norm nonneg a218ca485846
-- statement:
--   The P2 M Ground Theory Heights  Heights Herm Norm li norm nonneg a218ca485846 construction uses the P2 M Ground Theory Heights  Heights Herm Norm li norm nonneg a218ca485846 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L16-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L16-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere
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
open MeasureTheory Set MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.HermNorm
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_HermNorm_li_norm_nonneg_a218ca485846 (h : HermNorm n) (v : Fin n → ℂ) : 0 ≤ h.norm v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermNorm».«li_norm_nonneg» := P2M_GroundTheory_Heights__Heights_HermNorm_li_norm_nonneg_a218ca485846
