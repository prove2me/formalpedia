-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_ker_toSub_0f000c74cea3
-- name    : P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_ker_toSub_0f000c74cea3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:48.068827+00:00
-- url     : https://prove2.me/theorems/8fcce40d-5f55-40af-9fd9-a52f86e7074b
-- title:
--   P2 M Ground Theory Heights  Heights Chart Max Ideals ker to Sub 0f000c74cea3: P2 M Ground Theory Heights  Heights Chart Max Ideals ker to Sub 0f000c74cea3
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Max Ideals ker to Sub 0f000c74cea3 construction uses the P2 M Ground Theory Heights  Heights Chart Max Ideals ker to Sub 0f000c74cea3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartMaxIdeals.lean#L36-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartMaxIdeals.lean#L36-L58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProperSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartMaxIdeals
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
open GroundTheory.Heights₂.Heights.ChartMaxIdeals
variable {F : Type} [Field F] {n e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_ker_toSub_0f000c74cea3 {I W : Ideal (MvPolynomial (Fin n) F)} (h : I ≤ W) (t : Fin n → F) :
    RingHom.ker (toSub h t e) = W.map (chartX I t e) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMaxIdeals».«ker_toSub» := P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_ker_toSub_0f000c74cea3
