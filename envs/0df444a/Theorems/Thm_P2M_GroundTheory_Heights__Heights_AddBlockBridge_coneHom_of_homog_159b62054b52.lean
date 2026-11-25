-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockBridge_coneHom_of_homog_159b62054b52
-- name    : P2M_GroundTheory_Heights__Heights_AddBlockBridge_coneHom_of_homog_159b62054b52
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:14:40.854603+00:00
-- url     : https://prove2.me/theorems/9ef0ff92-3543-4b12-beda-df7ab0f988f6
-- title:
--   P2 M Ground Theory Heights  Heights Add Block Bridge cone Hom of homog 159b62054b52: P2 M Ground Theory Heights  Heights Add Block Bridge cone Hom of homog 159b62054b52
-- statement:
--   The P2 M Ground Theory Heights  Heights Add Block Bridge cone Hom of homog 159b62054b52 construction uses the P2 M Ground Theory Heights  Heights Add Block Bridge cone Hom of homog 159b62054b52 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PAddHeightsridge.lean#L44-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PAddHeightsridge.lean#L44-L60

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

theorem P2M_GroundTheory_Heights__Heights_AddBlockBridge_coneHom_of_homog_159b62054b52 (y : Coord n → Ω) {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ}
    (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    coneHom y f = constMap ι (aeval y f) * ∏ k, varT k ^ δ k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AddBlockBridge».«coneHom_of_homog» := P2M_GroundTheory_Heights__Heights_AddBlockBridge_coneHom_of_homog_159b62054b52
