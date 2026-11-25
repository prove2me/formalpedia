-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_comap_chartX_map_2fbd012a6e92
-- name    : P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_comap_chartX_map_2fbd012a6e92
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:16:16.45839+00:00
-- url     : https://prove2.me/theorems/a50891ac-9ed6-5e83-8fe0-ed0a18f68fca
-- title:
--   P2 M Ground Theory Heights  Heights Chart Max Ideals comap chart X map 2fbd012a6e92: P2 M Ground Theory Heights  Heights Chart Max Ideals comap chart X map 2fbd012a6e92
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Max Ideals comap chart X map 2fbd012a6e92 construction uses the P2 M Ground Theory Heights  Heights Chart Max Ideals comap chart X map 2fbd012a6e92 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartMaxIdeals.lean#L69-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartMaxIdeals.lean#L69-L71

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

theorem P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_comap_chartX_map_2fbd012a6e92 {I W : Ideal (MvPolynomial (Fin n) F)} (h : I ≤ W) (t : Fin n → F) :
    (W.map (chartX I t e)).comap (chartX I t e) = RingHom.ker (chartX W t e) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMaxIdeals».«comap_chartX_map» := P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_comap_chartX_map_2fbd012a6e92
