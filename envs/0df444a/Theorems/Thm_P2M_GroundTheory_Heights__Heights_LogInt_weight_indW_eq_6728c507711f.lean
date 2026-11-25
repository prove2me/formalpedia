-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_weight_indW_eq_6728c507711f
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_weight_indW_eq_6728c507711f
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:27:58.800636+00:00
-- url     : https://prove2.me/theorems/1b862ba4-9cca-434c-9ef9-dcb1cc22554f
-- title:
--   P2 M Ground Theory Heights  Heights Log Int weight ind W eq 6728c507711f: P2 M Ground Theory Heights  Heights Log Int weight ind W eq 6728c507711f
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int weight ind W eq 6728c507711f construction uses the P2 M Ground Theory Heights  Heights Log Int weight ind W eq 6728c507711f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L163-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L163-L168

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntCircle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
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
open MeasureTheory Set MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
variable {ι : Type*}

theorem P2M_GroundTheory_Heights__Heights_LogInt_weight_indW_eq_6728c507711f (x : ι) [DecidableEq ι] (m : ι →₀ ℕ) :
    Finsupp.weight (indW (· = x)) m = m x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«weight_indW_eq» := P2M_GroundTheory_Heights__Heights_LogInt_weight_indW_eq_6728c507711f
