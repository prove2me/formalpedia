-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_normT_mem_polydisc_262f8e73a463
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_normT_mem_polydisc_262f8e73a463
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:28:05.363182+00:00
-- url     : https://prove2.me/theorems/ea183872-5cf1-4a2b-a28a-c61df5ca6651
-- title:
--   P2 M Ground Theory Heights  Heights Log Int norm T mem polydisc 262f8e73a463: P2 M Ground Theory Heights  Heights Log Int norm T mem polydisc 262f8e73a463
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int norm T mem polydisc 262f8e73a463 construction uses the P2 M Ground Theory Heights  Heights Log Int norm T mem polydisc 262f8e73a463 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L135-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L135-L149

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

theorem P2M_GroundTheory_Heights__Heights_LogInt_normT_mem_polydisc_262f8e73a463 (h : HermNorm n) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ (v : Fin n → ℂ) (j : Fin n), ‖v j‖ ≤ C * h.norm v) (T : Finset (Fin k))
    (u : Fin k × Fin n → ℂ) (hu : u ∈ polydisc _ C) : normT h T u ∈ polydisc _ C := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«normT_mem_polydisc» := P2M_GroundTheory_Heights__Heights_LogInt_normT_mem_polydisc_262f8e73a463
