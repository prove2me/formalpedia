-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_weight_indW_le_126af73320e3
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_weight_indW_le_126af73320e3
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:41.213823+00:00
-- url     : https://prove2.me/theorems/66e719cc-e097-4a22-8198-623962b93e6b
-- title:
--   P2 M Ground Theory Heights  Heights Log Int weight ind W le 126af73320e3: P2 M Ground Theory Heights  Heights Log Int weight ind W le 126af73320e3
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int weight ind W le 126af73320e3 construction uses the P2 M Ground Theory Heights  Heights Log Int weight ind W le 126af73320e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L170-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L170-L173

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

theorem P2M_GroundTheory_Heights__Heights_LogInt_weight_indW_le_126af73320e3 (p : ι → Prop) [DecidablePred p] (m : ι →₀ ℕ) :
    Finsupp.weight (indW p) m ≤ m.sum fun _ e => e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«weight_indW_le» := P2M_GroundTheory_Heights__Heights_LogInt_weight_indW_le_126af73320e3
