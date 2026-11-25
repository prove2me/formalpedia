-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalDivisor_divCycle_of_mem_a95e3337f26a
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalDivisor_divCycle_of_mem_a95e3337f26a
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:24:06.668798+00:00
-- url     : https://prove2.me/theorems/541479a8-fecb-4c65-ab0b-e46bba33bac8
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Divisor div Cycle of mem a95e3337f26a: P2 M Ground Theory Heights  Heights Inter Diagonal Divisor div Cycle of mem a95e3337f26a
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Divisor div Cycle of mem a95e3337f26a construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Divisor div Cycle of mem a95e3337f26a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagDiv.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagDiv.lean#L17-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagDiv
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalDivisor
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalDivisor_divCycle_of_mem_a95e3337f26a {P W : Ideal (MRing ι)} {s : MRing ι} (hW : W ∈ divSupp P s) :
    divCycle P s W = multAt (P ⊔ Ideal.span {s}) W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalDivisor».«divCycle_of_mem» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalDivisor_divCycle_of_mem_a95e3337f26a
