-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularityFunctionFieldNumber_specMap_form_ff00a8b1a3cb
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RegularityFunctionFieldNumber_specMap_form_ff00a8b1a3cb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:00:30.088873+00:00
-- url     : https://prove2.me/theorems/f77510b8-fbd1-4073-9ad9-24edee111e87
-- title:
--   P2 M Ground Theory Heights  Heights Inter Regularity Function Field Number spec Map form ff00a8b1a3cb: P2 M Ground Theory Heights  Heights Inter Regularity Function Field Number spec Map form ff00a8b1
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Regularity Function Field Number spec Map form ff00a8b1a3cb construction uses the P2 M Ground Theory Heights  Heights Inter Regularity Function Field Number spec Map form ff00a8b1a3cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/FunFieldLeLocRing.lean#L33-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/FunFieldLeLocRing.lean#L33-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotMemOfNonZeroDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PHorizNotMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FunFieldLeLocRing
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
open GroundTheory.Heights₂.Heights.Inter.RegularityFunctionFieldNumber
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable [DecidableEq K] {E : Type*} [Field E]

theorem P2M_GroundTheory_Heights__Heights_Inter_RegularityFunctionFieldNumber_specMap_form_ff00a8b1a3cb (ψ : MRing ι →+* E) (S : Finset K) {g : MRing ι} {a : K → ℕ} (hg : IsMultiHomog g a) :
    specMap ψ S g = (∏ k, cS E S k ^ a k) * MvPolynomial.C (ψ g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RegularityFunctionFieldNumber».«specMap_form» := P2M_GroundTheory_Heights__Heights_Inter_RegularityFunctionFieldNumber_specMap_form_ff00a8b1a3cb
