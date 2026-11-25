-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsChowFormCycle_ne_zero_b5ee6986b005
-- name    : P2M_GroundTheory_Heights__Heights_IsChowFormCycle_ne_zero_b5ee6986b005
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:44:44.007864+00:00
-- url     : https://prove2.me/theorems/bef781e2-8736-448c-aa5f-0ec194a516a9
-- title:
--   P2 M Ground Theory Heights  Heights Is Chow Form Cycle ne zero b5ee6986b005: P2 M Ground Theory Heights  Heights Is Chow Form Cycle ne zero b5ee6986b005
-- statement:
--   The P2 M Ground Theory Heights  Heights Is Chow Form Cycle ne zero b5ee6986b005 construction uses the P2 M Ground Theory Heights  Heights Is Chow Form Cycle ne zero b5ee6986b005 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PDefectAverage.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PDefectAverage.lean#L9-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PDefectAverage
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
open MvPolynomial MeasureTheory

theorem P2M_GroundTheory_Heights__Heights_IsChowFormCycle_ne_zero_b5ee6986b005 {n k : ℕ} {Z : ProjCycle ℂ n} {f : MvPolynomial (Fin k × Fin n) ℂ}
    (hf : IsChowFormCycle Z k f) : f ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IsChowFormCycle».«ne_zero» := P2M_GroundTheory_Heights__Heights_IsChowFormCycle_ne_zero_b5ee6986b005
