-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_whole_ringKrullDim_b53d304dea6b
-- name    : P2M_GroundTheory_Heights__Heights_whole_ringKrullDim_b53d304dea6b
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:50:55.344878+00:00
-- url     : https://prove2.me/theorems/61180c11-d8ee-4c63-aedd-e5a1c23f798d
-- title:
--   P2 M Ground Theory Heights  Heights whole ring Krull Dim b53d304dea6b: P2 M Ground Theory Heights  Heights whole ring Krull Dim b53d304dea6b
-- statement:
--   The P2 M Ground Theory Heights  Heights whole ring Krull Dim b53d304dea6b construction uses the P2 M Ground Theory Heights  Heights whole ring Krull Dim b53d304dea6b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L198-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L198-L210

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
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
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (n : ι → ℕ) (k₀ : ι)

theorem P2M_GroundTheory_Heights__Heights_whole_ringKrullDim_b53d304dea6b (N : ℕ) :
    ringKrullDim (ArithVariety.whole (fun _ : Unit ↦ N)).CoordRing =
      ((N + 1 + Fintype.card Unit : ℕ) : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«whole_ringKrullDim» := P2M_GroundTheory_Heights__Heights_whole_ringKrullDim_b53d304dea6b
