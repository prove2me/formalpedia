-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_algebraMap_linForm_2ec74aa66477
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_algebraMap_linForm_2ec74aa66477
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:12:56.96454+00:00
-- url     : https://prove2.me/theorems/7c785369-9247-42b1-b532-99dfa918584c
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow Div Cycle Generic algebra Map lin Form 2ec74aa66477: P2 M Ground Theory Heights  Heights Objects Chow Div Cycle Generic algebra Map lin Form 2ec74aa664
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow Div Cycle Generic algebra Map lin Form 2ec74aa66477 construction uses the P2 M Ground Theory Heights  Heights Objects Chow Div Cycle Generic algebra Map lin Form 2ec74aa66477 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PObjectsDivCycleGeneric.lean#L110-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PObjectsDivCycleGeneric.lean#L110-L113

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_algebraMap_linForm_2ec74aa66477 (u : Fin n → ℤ) :
    algebraMap _ (MvPolynomial (Fin n) ℚ) (IndefiniteRowSideFullHecke.ArithBezout.linForm u) = linForm fun j => (u j : ℚ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«DivCycleGeneric».«algebraMap_linForm» := P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_algebraMap_linForm_2ec74aa66477
