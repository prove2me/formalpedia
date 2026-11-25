-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecSeparable_secCoord_chart_2b705866370f
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_GenSecSeparable_secCoord_chart_2b705866370f
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:43:12.572839+00:00
-- url     : https://prove2.me/theorems/c953b949-a7a8-40ea-ba0d-9f47609e58f8
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Gen Sec Separable sec Coord chart 2b705866370f: P2 M Ground Theory Heights  Heights Vertical Gen Sec Separable sec Coord chart 2b705866370f
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Gen Sec Separable sec Coord chart 2b705866370f construction uses the P2 M Ground Theory Heights  Heights Vertical Gen Sec Separable sec Coord chart 2b705866370f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecSeparable.lean#L45-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecSeparable.lean#L45-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChartPointTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsSecPointSeparable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenSecSeparable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.GenSecSeparable

theorem P2M_GroundTheory_Heights__Heights_Vertical_GenSecSeparable_secCoord_chart_2b705866370f {E : Type*} [Field E] {n e : ℕ} (Q : Ideal (MvPolynomial (Fin n) E))
    (y : Par e n → E) : ∑ j, algebraMap E (SecAlg Q y) (y (.inr j)) * secCoord Q y j = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«GenSecSeparable».«secCoord_chart» := P2M_GroundTheory_Heights__Heights_Vertical_GenSecSeparable_secCoord_chart_2b705866370f
