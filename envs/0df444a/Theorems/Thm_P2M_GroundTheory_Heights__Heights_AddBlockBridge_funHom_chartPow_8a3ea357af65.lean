-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockBridge_funHom_chartPow_8a3ea357af65
-- name    : P2M_GroundTheory_Heights__Heights_AddBlockBridge_funHom_chartPow_8a3ea357af65
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:15:37.566321+00:00
-- url     : https://prove2.me/theorems/bde29f08-077e-4c93-ab7a-4a88b788eb9f
-- title:
--   P2 M Ground Theory Heights  Heights Add Block Bridge fun Hom chart Pow 8a3ea357af65: P2 M Ground Theory Heights  Heights Add Block Bridge fun Hom chart Pow 8a3ea357af65
-- statement:
--   The P2 M Ground Theory Heights  Heights Add Block Bridge fun Hom chart Pow 8a3ea357af65 construction uses the P2 M Ground Theory Heights  Heights Add Block Bridge fun Hom chart Pow 8a3ea357af65 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PAddHeightsridge.lean#L92-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PAddHeightsridge.lean#L92-L96

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
variable (P : ArithVariety n) (y : Coord n → Ω) (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y)

theorem P2M_GroundTheory_Heights__Heights_AddBlockBridge_funHom_chartPow_8a3ea357af65 (c : (k : ι) → Fin (n k + 1)) (a : ι → ℤ) :
    funHom P y hP (P.chartPow c a) = (∏ k, constMap ι (y ⟨k, c k⟩) ^ a k) * ∏ k, varT k ^ a k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AddBlockBridge».«funHom_chartPow» := P2M_GroundTheory_Heights__Heights_AddBlockBridge_funHom_chartPow_8a3ea357af65
