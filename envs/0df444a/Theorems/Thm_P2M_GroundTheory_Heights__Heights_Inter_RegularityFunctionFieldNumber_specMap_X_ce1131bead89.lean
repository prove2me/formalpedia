-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularityFunctionFieldNumber_specMap_X_ce1131bead89
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RegularityFunctionFieldNumber_specMap_X_ce1131bead89
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:50:07.165472+00:00
-- url     : https://prove2.me/theorems/d39bbba9-eeed-5f2d-a630-bb496b16df5c
-- title:
--   P2 M Ground Theory Heights  Heights Inter Regularity Function Field Number spec Map X ce1131bead89: P2 M Ground Theory Heights  Heights Inter Regularity Function Field Number spec Map X ce1131bead89
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Regularity Function Field Number spec Map X ce1131bead89 construction uses the P2 M Ground Theory Heights  Heights Inter Regularity Function Field Number spec Map X ce1131bead89 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/FunFieldLeLocRing.lean#L30-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/FunFieldLeLocRing.lean#L30-L31

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
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_RegularityFunctionFieldNumber_specMap_X_ce1131bead89 (ψ : MRing ι →+* E) (S : Finset K) (p : Σ k, ι k) :
    specMap ψ S (X p) = cS E S p.1 * MvPolynomial.C (ψ (X p)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RegularityFunctionFieldNumber».«specMap_X» := P2M_GroundTheory_Heights__Heights_Inter_RegularityFunctionFieldNumber_specMap_X_ce1131bead89
