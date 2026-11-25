-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_algebraMap_mem_chartRing_line_3298f58654f8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_algebraMap_mem_chartRing_line_3298f58654f8
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:59:48.532189+00:00
-- url     : https://prove2.me/theorems/3bf8958b-41a4-4651-aade-a21bf02b152e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman algebra Map mem chart Ring line 3298f58654f8: P2 M Ground Theory Heights  Heights Kleiman algebra Map mem chart Ring line 3298f58654f8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman algebra Map mem chart Ring line 3298f58654f8 construction uses the P2 M Ground Theory Heights  Heights Kleiman algebra Map mem chart Ring line 3298f58654f8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/AlgebraMapMemChartRingLine.lean#L406-L421
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/AlgebraMapMemChartRingLine.lean#L406-L421

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u v w
variable (k : Type u) [Field k]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_algebraMap_mem_chartRing_line_3298f58654f8 (p : Polynomial k) :
    algebraMap (Polynomial k) (RatFunc k) p ∈ chartRing k (lineX k) (lineChart0 k) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«algebraMap_mem_chartRing_line» := P2M_GroundTheory_Heights__Heights_Kleiman_algebraMap_mem_chartRing_line_3298f58654f8
