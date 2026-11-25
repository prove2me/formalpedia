-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockBridge_ne_zero_of_isLive_fba38c539105
-- name    : P2M_GroundTheory_Heights__Heights_AddBlockBridge_ne_zero_of_isLive_fba38c539105
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:15:43.51631+00:00
-- url     : https://prove2.me/theorems/f2e01d7e-a4b2-42a0-a4b9-492daec82438
-- title:
--   P2 M Ground Theory Heights  Heights Add Block Bridge ne zero of is Live fba38c539105: P2 M Ground Theory Heights  Heights Add Block Bridge ne zero of is Live fba38c539105
-- statement:
--   The P2 M Ground Theory Heights  Heights Add Block Bridge ne zero of is Live fba38c539105 construction uses the P2 M Ground Theory Heights  Heights Add Block Bridge ne zero of is Live fba38c539105 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PAddHeightsridge.lean#L82-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PAddHeightsridge.lean#L82-L85

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
include hP

theorem P2M_GroundTheory_Heights__Heights_AddBlockBridge_ne_zero_of_isLive_fba38c539105 {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) (k : ι) : y ⟨k, c k⟩ ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AddBlockBridge».«ne_zero_of_isLive» := P2M_GroundTheory_Heights__Heights_AddBlockBridge_ne_zero_of_isLive_fba38c539105
