-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecSeparable_adjoin_secCoord_b7d33270686f
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_GenSecSeparable_adjoin_secCoord_b7d33270686f
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:43:28.771868+00:00
-- url     : https://prove2.me/theorems/d3fe49af-7c96-4130-a13a-9ccca50cf25f
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Gen Sec Separable adjoin sec Coord b7d33270686f: P2 M Ground Theory Heights  Heights Vertical Gen Sec Separable adjoin sec Coord b7d33270686f
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Gen Sec Separable adjoin sec Coord b7d33270686f construction uses the P2 M Ground Theory Heights  Heights Vertical Gen Sec Separable adjoin sec Coord b7d33270686f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecSeparable.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecSeparable.lean#L27-L32

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_GenSecSeparable_adjoin_secCoord_b7d33270686f {E : Type*} [Field E] {n e : ℕ} (Q : Ideal (MvPolynomial (Fin n) E))
    (y : Par e n → E) : Algebra.adjoin E (Set.range (secCoord Q y)) = ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«GenSecSeparable».«adjoin_secCoord» := P2M_GroundTheory_Heights__Heights_Vertical_GenSecSeparable_adjoin_secCoord_b7d33270686f
