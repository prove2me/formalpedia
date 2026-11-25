-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_mem_divSupp_of_mem_40c415dfdd3f
-- name    : P2M_GroundTheory_Heights__Heights_Inter_mem_divSupp_of_mem_40c415dfdd3f
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:23:57.706679+00:00
-- url     : https://prove2.me/theorems/85ba1b7d-bdd6-41b2-8a73-b68284ec5752
-- title:
--   P2 M Ground Theory Heights  Heights Inter mem div Supp of mem 40c415dfdd3f: P2 M Ground Theory Heights  Heights Inter mem div Supp of mem 40c415dfdd3f
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter mem div Supp of mem 40c415dfdd3f construction uses the P2 M Ground Theory Heights  Heights Inter mem div Supp of mem 40c415dfdd3f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotLtLtOfMemMinimalPrimes.lean#L112-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotLtLtOfMemMinimalPrimes.lean#L112-L114

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

theorem P2M_GroundTheory_Heights__Heights_Inter_mem_divSupp_of_mem_40c415dfdd3f {P W : Ideal (MRing ι)} [P.IsPrime] {s t : MRing ι}
    (hW : W ∈ divSupp P s) (htP : t ∉ P) (htW : t ∈ W) : W ∈ divSupp P t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«mem_divSupp_of_mem» := P2M_GroundTheory_Heights__Heights_Inter_mem_divSupp_of_mem_40c415dfdd3f
