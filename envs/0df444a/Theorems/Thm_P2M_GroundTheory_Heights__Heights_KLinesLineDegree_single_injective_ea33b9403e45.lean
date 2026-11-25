-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesLineDegree_single_injective_ea33b9403e45
-- name    : P2M_GroundTheory_Heights__Heights_KLinesLineDegree_single_injective_ea33b9403e45
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:56.102156+00:00
-- url     : https://prove2.me/theorems/4dfee5f8-6d21-584b-96ca-03fa5b2297e5
-- title:
--   P2 M Ground Theory Heights  Heights KLines Line Degree single injective ea33b9403e45: P2 M Ground Theory Heights  Heights KLines Line Degree single injective ea33b9403e45
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Line Degree single injective ea33b9403e45 construction uses the P2 M Ground Theory Heights  Heights KLines Line Degree single injective ea33b9403e45 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesLineDegree.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesLineDegree.lean#L23-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesLineDegree
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
open NumberField Matrix
open scoped nonZeroDivisors
noncomputable section
open GroundTheory.Heights₂.Heights.KLinesLineDegree
variable {K : Type} [Field K] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_KLinesLineDegree_single_injective_ea33b9403e45 (x : Fin n) :
    Function.Injective (AddMonoidHom.single (fun _ : Fin n => K) x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesLineDegree».«single_injective» := P2M_GroundTheory_Heights__Heights_KLinesLineDegree_single_injective_ea33b9403e45
