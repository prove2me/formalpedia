-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_genericIdeal_eq_ab3f42321e11
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_genericIdeal_eq_ab3f42321e11
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:13:18.644799+00:00
-- url     : https://prove2.me/theorems/0796b1c2-2d00-446b-b2df-2eed068923c8
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow Div Cycle Generic generic Ideal eq ab3f42321e11: P2 M Ground Theory Heights  Heights Objects Chow Div Cycle Generic generic Ideal eq ab3f42321e11
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow Div Cycle Generic generic Ideal eq ab3f42321e11 construction uses the P2 M Ground Theory Heights  Heights Objects Chow Div Cycle Generic generic Ideal eq ab3f42321e11 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PObjectsDivCycleGeneric.lean#L88-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PObjectsDivCycleGeneric.lean#L88-L96

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PObjectsDivCycleGeneric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open GroundTheory.Heights₂.Heights.ObjectsChow.DivCycleGeneric
open MvPolynomial
variable {n : ℕ}
attribute [local instance] genericAlgebra

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_genericIdeal_eq_ab3f42321e11 (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n))) :
    genericIdeal W = W.map (algebraMap _ (MvPolynomial (Fin n) ℚ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«DivCycleGeneric».«genericIdeal_eq» := P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_genericIdeal_eq_ab3f42321e11
