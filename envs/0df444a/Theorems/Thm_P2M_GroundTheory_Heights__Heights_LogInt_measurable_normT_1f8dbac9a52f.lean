-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_measurable_normT_1f8dbac9a52f
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_measurable_normT_1f8dbac9a52f
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:35.993578+00:00
-- url     : https://prove2.me/theorems/36637343-abb5-4eff-af33-6a9e10583cc9
-- title:
--   P2 M Ground Theory Heights  Heights Log Int measurable norm T 1f8dbac9a52f: P2 M Ground Theory Heights  Heights Log Int measurable norm T 1f8dbac9a52f
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int measurable norm T 1f8dbac9a52f construction uses the P2 M Ground Theory Heights  Heights Log Int measurable norm T 1f8dbac9a52f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L89-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L89-L96

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
open GroundTheory.Heights₂.Heights.LogInt
variable {n k : ℕ}

theorem P2M_GroundTheory_Heights__Heights_LogInt_measurable_normT_1f8dbac9a52f (h : HermNorm n) (T : Finset (Fin k)) : Measurable (normT h T) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«measurable_normT» := P2M_GroundTheory_Heights__Heights_LogInt_measurable_normT_1f8dbac9a52f
