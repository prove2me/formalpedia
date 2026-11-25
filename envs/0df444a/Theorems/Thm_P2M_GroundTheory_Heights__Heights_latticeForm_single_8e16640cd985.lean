-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_latticeForm_single_8e16640cd985
-- name    : P2M_GroundTheory_Heights__Heights_latticeForm_single_8e16640cd985
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:47:34.862576+00:00
-- url     : https://prove2.me/theorems/a51d6747-a769-4a41-9a7a-ad0c88b18b8a
-- title:
--   P2 M Ground Theory Heights  Heights lattice Form single 8e16640cd985: P2 M Ground Theory Heights  Heights lattice Form single 8e16640cd985
-- statement:
--   The P2 M Ground Theory Heights  Heights lattice Form single 8e16640cd985 construction uses the P2 M Ground Theory Heights  Heights lattice Form single 8e16640cd985 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockPoints.lean#L165-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockPoints.lean#L165-L168

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

theorem P2M_GroundTheory_Heights__Heights_latticeForm_single_8e16640cd985 {m : ℕ} (j : Fin m) (a : K) :
    latticeForm (Pi.single j a : Fin m → K) = C a * X j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«latticeForm_single» := P2M_GroundTheory_Heights__Heights_latticeForm_single_8e16640cd985
