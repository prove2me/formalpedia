-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_continuous_l2Norm_de9fc54faefe
-- name    : P2M_GroundTheory_Heights__Heights_continuous_l2Norm_de9fc54faefe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:29:16.835108+00:00
-- url     : https://prove2.me/theorems/d972d79b-e29b-4205-8812-2842de7c02fc
-- title:
--   P2 M Ground Theory Heights  Heights continuous l2 Norm de9fc54faefe: P2 M Ground Theory Heights  Heights continuous l2 Norm de9fc54faefe
-- statement:
--   The P2 M Ground Theory Heights  Heights continuous l2 Norm de9fc54faefe construction uses the P2 M Ground Theory Heights  Heights continuous l2 Norm de9fc54faefe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Comparison.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Comparison.lean#L33-L35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Comparison
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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_continuous_l2Norm_de9fc54faefe {m : ℕ} : Continuous (fun w : Fin m → ℂ ↦ l2Norm w) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«continuous_l2Norm» := P2M_GroundTheory_Heights__Heights_continuous_l2Norm_de9fc54faefe
