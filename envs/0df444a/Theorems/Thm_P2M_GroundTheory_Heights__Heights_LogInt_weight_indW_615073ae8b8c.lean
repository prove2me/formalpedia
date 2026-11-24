-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_weight_indW_615073ae8b8c
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_weight_indW_615073ae8b8c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:42.00959+00:00
-- url     : https://prove2.me/theorems/ea259c1b-79fa-4949-b5ab-2ad7ba07153c
-- title:
--   P2 M Ground Theory Heights  Heights Log Int weight ind W 615073ae8b8c: P2 M Ground Theory Heights  Heights Log Int weight ind W 615073ae8b8c
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int weight ind W 615073ae8b8c construction uses the P2 M Ground Theory Heights  Heights Log Int weight ind W 615073ae8b8c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L23-L27

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

theorem P2M_GroundTheory_Heights__Heights_LogInt_weight_indW_615073ae8b8c (p : ι → Prop) [DecidablePred p] (m : ι →₀ ℕ) :
    Finsupp.weight (indW p) m = ∑ i ∈ m.support, if p i then m i else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«weight_indW» := P2M_GroundTheory_Heights__Heights_LogInt_weight_indW_615073ae8b8c
