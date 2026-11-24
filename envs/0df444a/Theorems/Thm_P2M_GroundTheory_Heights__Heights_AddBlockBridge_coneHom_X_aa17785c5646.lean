-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockBridge_coneHom_X_aa17785c5646
-- name    : P2M_GroundTheory_Heights__Heights_AddBlockBridge_coneHom_X_aa17785c5646
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:59:18.245302+00:00
-- url     : https://prove2.me/theorems/81593cad-f416-49d6-a98f-70d4299e4c98
-- title:
--   P2 M Ground Theory Heights  Heights Add Block Bridge cone Hom X aa17785c5646: P2 M Ground Theory Heights  Heights Add Block Bridge cone Hom X aa17785c5646
-- statement:
--   The P2 M Ground Theory Heights  Heights Add Block Bridge cone Hom X aa17785c5646 construction uses the P2 M Ground Theory Heights  Heights Add Block Bridge cone Hom X aa17785c5646 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PAddHeightsridge.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PAddHeightsridge.lean#L35-L37

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

theorem P2M_GroundTheory_Heights__Heights_AddBlockBridge_coneHom_X_aa17785c5646 (y : Coord n → Ω) (v : Coord n) : coneHom y (X v) = constMap ι (y v) * varT v.1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AddBlockBridge».«coneHom_X» := P2M_GroundTheory_Heights__Heights_AddBlockBridge_coneHom_X_aa17785c5646
