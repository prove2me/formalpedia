-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecSeparable_secCoord_form_ecd479731ca9
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_GenSecSeparable_secCoord_form_ecd479731ca9
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:42:43.448601+00:00
-- url     : https://prove2.me/theorems/07e111e7-6226-5d32-9aba-016727e3c82a
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Gen Sec Separable sec Coord form ecd479731ca9: P2 M Ground Theory Heights  Heights Vertical Gen Sec Separable sec Coord form ecd479731ca9
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Gen Sec Separable sec Coord form ecd479731ca9 construction uses the P2 M Ground Theory Heights  Heights Vertical Gen Sec Separable sec Coord form ecd479731ca9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecSeparable.lean#L34-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecSeparable.lean#L34-L43

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_GenSecSeparable_secCoord_form_ecd479731ca9 {E : Type*} [Field E] {n e : ℕ} (Q : Ideal (MvPolynomial (Fin n) E))
    (y : Par e n → E) (i : Fin e) :
    ∑ j, algebraMap E (SecAlg Q y) (y (.inl (i, j))) * secCoord Q y j = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«GenSecSeparable».«secCoord_form» := P2M_GroundTheory_Heights__Heights_Vertical_GenSecSeparable_secCoord_form_ecd479731ca9
