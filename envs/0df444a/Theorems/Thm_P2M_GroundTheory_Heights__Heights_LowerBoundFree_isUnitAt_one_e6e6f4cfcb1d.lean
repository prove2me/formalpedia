-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isUnitAt_one_e6e6f4cfcb1d
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_isUnitAt_one_e6e6f4cfcb1d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:28:30.239533+00:00
-- url     : https://prove2.me/theorems/fb9729e7-e1dd-4bb5-9f82-88062643e58f
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free is Unit At one e6e6f4cfcb1d: P2 M Ground Theory Heights  Heights Lower Bound Free is Unit At one e6e6f4cfcb1d
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free is Unit At one e6e6f4cfcb1d construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free is Unit At one e6e6f4cfcb1d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/MemMCoordIdealOfAevalEqZero.lean#L102-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/MemMCoordIdealOfAevalEqZero.lean#L102-L103

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_isUnitAt_one_e6e6f4cfcb1d (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) : IsUnitAt y 1 z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«isUnitAt_one» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_isUnitAt_one_e6e6f4cfcb1d
