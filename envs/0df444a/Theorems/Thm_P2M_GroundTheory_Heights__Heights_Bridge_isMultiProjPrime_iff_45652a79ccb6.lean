-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_isMultiProjPrime_iff_45652a79ccb6
-- name    : P2M_GroundTheory_Heights__Heights_Bridge_isMultiProjPrime_iff_45652a79ccb6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:42.799014+00:00
-- url     : https://prove2.me/theorems/f80861b1-8a2a-4505-9e20-f147af2de021
-- title:
--   P2 M Ground Theory Heights  Heights Bridge is Multi Proj Prime iff 45652a79ccb6: P2 M Ground Theory Heights  Heights Bridge is Multi Proj Prime iff 45652a79ccb6
-- statement:
--   The P2 M Ground Theory Heights  Heights Bridge is Multi Proj Prime iff 45652a79ccb6 construction uses the P2 M Ground Theory Heights  Heights Bridge is Multi Proj Prime iff 45652a79ccb6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/IsMultiHomogIdealIff.lean#L79-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/IsMultiHomogIdealIff.lean#L79-L82

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Bridge
open MvPolynomial
noncomputable section
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
variable [DecidableEq K] [∀ k, Fintype (ι k)]
attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem P2M_GroundTheory_Heights__Heights_Bridge_isMultiProjPrime_iff_45652a79ccb6 (P : Ideal (NumbersDVR.MRing ι R)) :
    NumbersDVR.IsMultiProjPrime P ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime (R := R) P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Bridge».«isMultiProjPrime_iff» := P2M_GroundTheory_Heights__Heights_Bridge_isMultiProjPrime_iff_45652a79ccb6
