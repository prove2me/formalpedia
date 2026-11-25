-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_comap_algebraMap_map_5533eb7a3b9c
-- name    : P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_comap_algebraMap_map_5533eb7a3b9c
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:16:10.385897+00:00
-- url     : https://prove2.me/theorems/2f818a91-4bb8-5dfb-85e8-b063c300a8c8
-- title:
--   P2 M Ground Theory Heights  Heights Chart Max Ideals comap algebra Map map 5533eb7a3b9c: P2 M Ground Theory Heights  Heights Chart Max Ideals comap algebra Map map 5533eb7a3b9c
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Max Ideals comap algebra Map map 5533eb7a3b9c construction uses the P2 M Ground Theory Heights  Heights Chart Max Ideals comap algebra Map map 5533eb7a3b9c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartMaxIdeals.lean#L73-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartMaxIdeals.lean#L73-L76

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

theorem P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_comap_algebraMap_map_5533eb7a3b9c {I W : Ideal (MvPolynomial (Fin n) F)} (h : I ≤ W) (t : Fin n → F) :
    (W.map (chartX I t e)).comap (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) =
      RingHom.ker (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc W t e)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMaxIdeals».«comap_algebraMap_map» := P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_comap_algebraMap_map_5533eb7a3b9c
