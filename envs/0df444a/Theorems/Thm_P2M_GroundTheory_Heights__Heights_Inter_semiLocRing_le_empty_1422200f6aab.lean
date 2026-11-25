-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_semiLocRing_le_empty_1422200f6aab
-- name    : P2M_GroundTheory_Heights__Heights_Inter_semiLocRing_le_empty_1422200f6aab
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:34:04.272557+00:00
-- url     : https://prove2.me/theorems/c645f1ef-ea31-4735-abc0-e8a8021271b6
-- title:
--   P2 M Ground Theory Heights  Heights Inter semi Loc Ring le empty 1422200f6aab: P2 M Ground Theory Heights  Heights Inter semi Loc Ring le empty 1422200f6aab
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter semi Loc Ring le empty 1422200f6aab construction uses the P2 M Ground Theory Heights  Heights Inter semi Loc Ring le empty 1422200f6aab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocFinite.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocFinite.lean#L14-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsLocRingIntClosure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsLocRingDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocFinite
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

theorem P2M_GroundTheory_Heights__Heights_Inter_semiLocRing_le_empty_1422200f6aab {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (𝒲 : Set (Ideal (MRing ι))) : semiLocRing P 𝒲 ≤ semiLocRing P ∅ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«semiLocRing_le_empty» := P2M_GroundTheory_Heights__Heights_Inter_semiLocRing_le_empty_1422200f6aab
