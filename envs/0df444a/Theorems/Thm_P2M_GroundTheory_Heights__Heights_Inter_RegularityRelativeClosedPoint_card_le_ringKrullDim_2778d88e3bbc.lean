-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularityRelativeClosedPoint_card_le_ringKrullDim_2778d88e3bbc
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RegularityRelativeClosedPoint_card_le_ringKrullDim_2778d88e3bbc
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:42:41.570897+00:00
-- url     : https://prove2.me/theorems/3fd5f452-b9b9-4cfc-b520-cdfd597945d3
-- title:
--   P2 M Ground Theory Heights  Heights Inter Regularity Relative Closed Point card le ring Krull Dim 2778d88e3bbc: P2 M Ground Theory Heights  Heights Inter Regularity Relative Closed Point card le ring
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Regularity Relative Closed Point card le ring Krull Dim 2778d88e3bbc construction uses the P2 M Ground Theory Heights  Heights Inter Regularity Relative Closed Point card le ring Krull Dim 2778d88e3bbc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/CardLeRingKrullDim.lean#L55-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/CardLeRingKrullDim.lean#L55-L97

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreExtra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PHorizNotMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_CardLeRingKrullDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.RegularityRelativeClosedPoint
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_Inter_RegularityRelativeClosedPoint_card_le_ringKrullDim_2778d88e3bbc (W : Ideal (MRing ι)) [W.IsPrime] (hWh : IsMultiHomogIdeal W)
    (hWr : IsRelevant W) : ((Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι ⧸ W) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RegularityRelativeClosedPoint».«card_le_ringKrullDim» := P2M_GroundTheory_Heights__Heights_Inter_RegularityRelativeClosedPoint_card_le_ringKrullDim_2778d88e3bbc
