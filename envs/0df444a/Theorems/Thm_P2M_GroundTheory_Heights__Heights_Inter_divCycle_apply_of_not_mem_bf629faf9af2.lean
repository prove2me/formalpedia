-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_divCycle_apply_of_not_mem_bf629faf9af2
-- name    : P2M_GroundTheory_Heights__Heights_Inter_divCycle_apply_of_not_mem_bf629faf9af2
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:24:48.181129+00:00
-- url     : https://prove2.me/theorems/2d050197-95a3-4f0c-b180-d7fe61ac90c0
-- title:
--   P2 M Ground Theory Heights  Heights Inter div Cycle apply of not mem bf629faf9af2: P2 M Ground Theory Heights  Heights Inter div Cycle apply of not mem bf629faf9af2
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter div Cycle apply of not mem bf629faf9af2 construction uses the P2 M Ground Theory Heights  Heights Inter div Cycle apply of not mem bf629faf9af2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotLtLtOfMemMinimalPrimes.lean#L122-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotLtLtOfMemMinimalPrimes.lean#L122-L126

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotLtLtOfMemMinimalPrimes
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
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_divCycle_apply_of_not_mem_bf629faf9af2 {P W : Ideal (MRing ι)} {s : MRing ι} (h : W ∉ divSupp P s) :
    divCycle P s W = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«divCycle_apply_of_not_mem» := P2M_GroundTheory_Heights__Heights_Inter_divCycle_apply_of_not_mem_bf629faf9af2
