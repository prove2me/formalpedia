-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_secCoord_chart_58c3f1290d13
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_secCoord_chart_58c3f1290d13
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:44:36.857844+00:00
-- url     : https://prove2.me/theorems/671ff3ee-fd52-405d-964d-6d12bc72be31
-- title:
--   P2 M Ground Theory Heights  Heights Vertical sec Coord chart 58c3f1290d13: P2 M Ground Theory Heights  Heights Vertical sec Coord chart 58c3f1290d13
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical sec Coord chart 58c3f1290d13 construction uses the P2 M Ground Theory Heights  Heights Vertical sec Coord chart 58c3f1290d13 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChowNormFormGeneric.lean#L30-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChowNormFormGeneric.lean#L30-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChowNormFormGeneric
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

theorem P2M_GroundTheory_Heights__Heights_Vertical_secCoord_chart_58c3f1290d13 {E : Type*} [Field E] {n e : ℕ} (Q : Ideal (MvPolynomial (Fin n) E))
    (y : Par e n → E) : ∑ j, algebraMap E (SecAlg Q y) (y (.inr j)) * secCoord Q y j = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«secCoord_chart» := P2M_GroundTheory_Heights__Heights_Vertical_secCoord_chart_58c3f1290d13
