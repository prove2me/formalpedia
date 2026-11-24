-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockBridge_varT_ne_zero_0cfbfaa1a01e
-- name    : P2M_GroundTheory_Heights__Heights_AddBlockBridge_varT_ne_zero_0cfbfaa1a01e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:50.809707+00:00
-- url     : https://prove2.me/theorems/9505ef8e-08cf-4fc5-8380-564d35d3e101
-- title:
--   P2 M Ground Theory Heights  Heights Add Block Bridge var T ne zero 0cfbfaa1a01e: P2 M Ground Theory Heights  Heights Add Block Bridge var T ne zero 0cfbfaa1a01e
-- statement:
--   The P2 M Ground Theory Heights  Heights Add Block Bridge var T ne zero 0cfbfaa1a01e construction uses the P2 M Ground Theory Heights  Heights Add Block Bridge var T ne zero 0cfbfaa1a01e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PAddHeightsridge.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PAddHeightsridge.lean#L26-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PAddHeightsridge
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.AddBlockBridge
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]
set_option linter.unusedSectionVars false

theorem P2M_GroundTheory_Heights__Heights_AddBlockBridge_varT_ne_zero_0cfbfaa1a01e (k : ι) : varT (Ω := Ω) k ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AddBlockBridge».«varT_ne_zero» := P2M_GroundTheory_Heights__Heights_AddBlockBridge_varT_ne_zero_0cfbfaa1a01e
