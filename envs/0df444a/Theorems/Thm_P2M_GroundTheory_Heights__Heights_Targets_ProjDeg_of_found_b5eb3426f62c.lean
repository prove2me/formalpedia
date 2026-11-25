-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjDeg_of_found_b5eb3426f62c
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjDeg_of_found_b5eb3426f62c
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:41:09.595135+00:00
-- url     : https://prove2.me/theorems/8578d67c-1891-58fd-b7da-3508093f35fe
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Deg of found b5eb3426f62c: P2 M Ground Theory Heights  Heights Targets Proj Deg of found b5eb3426f62c
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Deg of found b5eb3426f62c construction uses the P2 M Ground Theory Heights  Heights Targets Proj Deg of found b5eb3426f62c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ProjDeg.lean#L57-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ProjDeg.lean#L57-L89

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsFieldIntersectionExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumRatSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsFnDegRelDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ProjDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjDeg_of_found_b5eb3426f62c (hPF : ProjectionFormulaDegree.Statement.{u})
    (hFn : FnDegRelDeg.Statement.{u}) {K K' : Type} [Fintype K] [Fintype K'] (F : Type u) [Field F]
    (ι : K → Type) [∀ k, Fintype (ι k)] (ι' : K' → Type) [∀ k, Fintype (ι' k)] :
    ReciprocityTheory.ChartRestriction.G.AI.I1.ProjDegStatement F ι ι' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjDeg».«of_found» := P2M_GroundTheory_Heights__Heights_Targets_ProjDeg_of_found_b5eb3426f62c
