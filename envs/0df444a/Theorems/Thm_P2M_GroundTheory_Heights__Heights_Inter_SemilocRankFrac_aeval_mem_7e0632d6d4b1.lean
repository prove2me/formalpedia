-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocRankFrac_aeval_mem_7e0632d6d4b1
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SemilocRankFrac_aeval_mem_7e0632d6d4b1
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:45:10.676267+00:00
-- url     : https://prove2.me/theorems/7cdded68-d65d-4b77-97ee-e75eb7c74be6
-- title:
--   P2 M Ground Theory Heights  Heights Inter Semiloc Rank Frac aeval mem 7e0632d6d4b1: P2 M Ground Theory Heights  Heights Inter Semiloc Rank Frac aeval mem 7e0632d6d4b1
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Semiloc Rank Frac aeval mem 7e0632d6d4b1 construction uses the P2 M Ground Theory Heights  Heights Inter Semiloc Rank Frac aeval mem 7e0632d6d4b1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocRankFrac.lean#L45-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocRankFrac.lean#L45-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocRankFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRankFracDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocChartRatio
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocRankFrac
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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter.SemilocRankFrac
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem P2M_GroundTheory_Heights__Heights_Inter_SemilocRankFrac_aeval_mem_7e0632d6d4b1 [Algebra ℚ Ω] (L : IntermediateField ℚ Ω) {y : (Σ k, ι k) → Ω} (hy : ∀ p, y p ∈ L)
    (u : MRing ι) : aeval y u ∈ L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SemilocRankFrac».«aeval_mem» := P2M_GroundTheory_Heights__Heights_Inter_SemilocRankFrac_aeval_mem_7e0632d6d4b1
