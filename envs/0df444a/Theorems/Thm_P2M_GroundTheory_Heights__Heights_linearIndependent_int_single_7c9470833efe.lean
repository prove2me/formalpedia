-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_linearIndependent_int_single_7c9470833efe
-- name    : P2M_GroundTheory_Heights__Heights_linearIndependent_int_single_7c9470833efe
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:47:58.42467+00:00
-- url     : https://prove2.me/theorems/0740c34e-ca0b-45e7-96bd-99975fb8ca8b
-- title:
--   P2 M Ground Theory Heights  Heights linear Independent int single 7c9470833efe: P2 M Ground Theory Heights  Heights linear Independent int single 7c9470833efe
-- statement:
--   The P2 M Ground Theory Heights  Heights linear Independent int single 7c9470833efe construction uses the P2 M Ground Theory Heights  Heights linear Independent int single 7c9470833efe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/DualModel.lean#L61-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/DualModel.lean#L61-L69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_DualModel
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
open MvPolynomial NumberField Matrix
open scoped ComplexOrder
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_linearIndependent_int_single_7c9470833efe (m : ℕ) :
    LinearIndependent ℤ (fun j : Fin m ↦ (Pi.single j (1 : ℚ) : Fin m → ℚ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«linearIndependent_int_single» := P2M_GroundTheory_Heights__Heights_linearIndependent_int_single_7c9470833efe
