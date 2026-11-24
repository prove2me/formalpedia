-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_isMultiHomogIdeal_iff_08bad36ad538
-- name    : P2M_GroundTheory_Heights__Heights_Bridge_isMultiHomogIdeal_iff_08bad36ad538
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:07.402212+00:00
-- url     : https://prove2.me/theorems/f1c39a0c-7d7e-4c70-a9ce-2510dea4547e
-- title:
--   P2 M Ground Theory Heights  Heights Bridge is Multi Homog Ideal iff 08bad36ad538: P2 M Ground Theory Heights  Heights Bridge is Multi Homog Ideal iff 08bad36ad538
-- statement:
--   The P2 M Ground Theory Heights  Heights Bridge is Multi Homog Ideal iff 08bad36ad538 construction uses the P2 M Ground Theory Heights  Heights Bridge is Multi Homog Ideal iff 08bad36ad538 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/IsMultiHomogIdealIff.lean#L55-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/IsMultiHomogIdealIff.lean#L55-L77

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

theorem P2M_GroundTheory_Heights__Heights_Bridge_isMultiHomogIdeal_iff_08bad36ad538 (P : Ideal (NumbersDVR.MRing ι R)) :
    NumbersDVR.IsMultiHomogIdeal P ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal (R := R) P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Bridge».«isMultiHomogIdeal_iff» := P2M_GroundTheory_Heights__Heights_Bridge_isMultiHomogIdeal_iff_08bad36ad538
