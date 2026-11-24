-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_support_fundCycle_iff_47043e9aed45
-- name    : P2M_GroundTheory_Heights__Heights_mem_support_fundCycle_iff_47043e9aed45
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:48:11.472983+00:00
-- url     : https://prove2.me/theorems/1f6b2ba1-476c-4491-960b-2687b5a3a361
-- title:
--   P2 M Ground Theory Heights  Heights mem support fund Cycle iff 47043e9aed45: P2 M Ground Theory Heights  Heights mem support fund Cycle iff 47043e9aed45
-- statement:
--   The P2 M Ground Theory Heights  Heights mem support fund Cycle iff 47043e9aed45 construction uses the P2 M Ground Theory Heights  Heights mem support fund Cycle iff 47043e9aed45 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormReduced.lean#L45-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormReduced.lean#L45-L57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LocalMultRadical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncIdealSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormReduced
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
open MvPolynomial
noncomputable section
variable {F : Type*} [Field F] {n k : ℕ}

theorem P2M_GroundTheory_Heights__Heights_mem_support_fundCycle_iff_47043e9aed45 {J : Ideal (MvPolynomial (Fin n) F)} (hJ : J.IsRadical)
    {W : Ideal (MvPolynomial (Fin n) F)} : W ∈ (fundCycle J).support ↔ W ∈ relComps J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mem_support_fundCycle_iff» := P2M_GroundTheory_Heights__Heights_mem_support_fundCycle_iff_47043e9aed45
