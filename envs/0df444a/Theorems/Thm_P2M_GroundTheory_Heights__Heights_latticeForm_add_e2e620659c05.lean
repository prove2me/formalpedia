-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_latticeForm_add_e2e620659c05
-- name    : P2M_GroundTheory_Heights__Heights_latticeForm_add_e2e620659c05
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:47:11.677392+00:00
-- url     : https://prove2.me/theorems/329a539c-7095-4da6-bc61-73f8b94e6f9b
-- title:
--   P2 M Ground Theory Heights  Heights lattice Form add e2e620659c05: P2 M Ground Theory Heights  Heights lattice Form add e2e620659c05
-- statement:
--   The P2 M Ground Theory Heights  Heights lattice Form add e2e620659c05 construction uses the P2 M Ground Theory Heights  Heights lattice Form add e2e620659c05 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockPoints.lean#L160-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockPoints.lean#L160-L162

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockPoints
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
open MvPolynomial NumberField
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable {r N : ℕ}
omit [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_latticeForm_add_e2e620659c05 {m : ℕ} (u v : Fin m → K) :
    latticeForm (u + v) = latticeForm u + latticeForm v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«latticeForm_add» := P2M_GroundTheory_Heights__Heights_latticeForm_add_e2e620659c05
