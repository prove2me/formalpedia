-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_normT_scaleP_74fbb51caf1a
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_normT_scaleP_74fbb51caf1a
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:27:51.161592+00:00
-- url     : https://prove2.me/theorems/1521301d-abd2-4b9d-89f3-b8a73952f64f
-- title:
--   P2 M Ground Theory Heights  Heights Log Int norm T scale P 74fbb51caf1a: P2 M Ground Theory Heights  Heights Log Int norm T scale P 74fbb51caf1a
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int norm T scale P 74fbb51caf1a construction uses the P2 M Ground Theory Heights  Heights Log Int norm T scale P 74fbb51caf1a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L106-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L106-L115

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

theorem P2M_GroundTheory_Heights__Heights_LogInt_normT_scaleP_74fbb51caf1a (h : HermNorm n) (T : Finset (Fin k)) (i : Fin k) (θ : ℝ)
    (u : Fin k × Fin n → ℂ) :
    normT h T (scaleP (inGroup i) (circleMap 0 1 θ) u) =
      scaleP (inGroup i) (circleMap 0 1 θ) (normT h T u) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«normT_scaleP» := P2M_GroundTheory_Heights__Heights_LogInt_normT_scaleP_74fbb51caf1a
