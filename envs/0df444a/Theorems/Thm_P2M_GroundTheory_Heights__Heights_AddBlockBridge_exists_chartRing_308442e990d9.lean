-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockBridge_exists_chartRing_308442e990d9
-- name    : P2M_GroundTheory_Heights__Heights_AddBlockBridge_exists_chartRing_308442e990d9
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:15:56.822123+00:00
-- url     : https://prove2.me/theorems/212f2dda-9b5e-40af-ae4a-4c755361f2e0
-- title:
--   P2 M Ground Theory Heights  Heights Add Block Bridge exists chart Ring 308442e990d9: P2 M Ground Theory Heights  Heights Add Block Bridge exists chart Ring 308442e990d9
-- statement:
--   The P2 M Ground Theory Heights  Heights Add Block Bridge exists chart Ring 308442e990d9 construction uses the P2 M Ground Theory Heights  Heights Add Block Bridge exists chart Ring 308442e990d9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PAddHeightsridge.lean#L98-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PAddHeightsridge.lean#L98-L114

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

theorem P2M_GroundTheory_Heights__Heights_AddBlockBridge_exists_chartRing_308442e990d9 (c : (k : ι) → Fin (n k + 1)) {r : Ω}
    (hr : r ∈ Geo.chartRingZ (ι := blockIdx n) y c) :
    ∃ η ∈ P.chartRing c, funHom P y hP η = constMap ι r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AddBlockBridge».«exists_chartRing» := P2M_GroundTheory_Heights__Heights_AddBlockBridge_exists_chartRing_308442e990d9
