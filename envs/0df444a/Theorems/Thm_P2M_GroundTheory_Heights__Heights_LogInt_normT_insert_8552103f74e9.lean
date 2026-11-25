-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_normT_insert_8552103f74e9
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_normT_insert_8552103f74e9
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:27:36.668681+00:00
-- url     : https://prove2.me/theorems/ae37f47e-2e53-4b59-ab2a-0591ef192bdb
-- title:
--   P2 M Ground Theory Heights  Heights Log Int norm T insert 8552103f74e9: P2 M Ground Theory Heights  Heights Log Int norm T insert 8552103f74e9
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int norm T insert 8552103f74e9 construction uses the P2 M Ground Theory Heights  Heights Log Int norm T insert 8552103f74e9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L117-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L117-L125

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

theorem P2M_GroundTheory_Heights__Heights_LogInt_normT_insert_8552103f74e9 (h : HermNorm n) (T : Finset (Fin k)) (i : Fin k) (hi : i ∉ T)
    (u : Fin k × Fin n → ℂ) :
    normT h (insert i T) u =
      scaleP (inGroup i) ((h.norm fun j => u (i, j) : ℝ) : ℂ)⁻¹ (normT h T u) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«normT_insert» := P2M_GroundTheory_Heights__Heights_LogInt_normT_insert_8552103f74e9
