-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_divCycle_eq_e8d03d8e52b7
-- name    : P2M_GroundTheory_Heights__Heights_Bridge_divCycle_eq_e8d03d8e52b7
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:16:01.035248+00:00
-- url     : https://prove2.me/theorems/617b5ad6-a55f-442e-9322-9437adf6a1ed
-- title:
--   P2 M Ground Theory Heights  Heights Bridge div Cycle eq e8d03d8e52b7: P2 M Ground Theory Heights  Heights Bridge div Cycle eq e8d03d8e52b7
-- statement:
--   The P2 M Ground Theory Heights  Heights Bridge div Cycle eq e8d03d8e52b7 construction uses the P2 M Ground Theory Heights  Heights Bridge div Cycle eq e8d03d8e52b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/IsMultiHomogIdealIff.lean#L93-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/IsMultiHomogIdealIff.lean#L93-L103

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

theorem P2M_GroundTheory_Heights__Heights_Bridge_divCycle_eq_e8d03d8e52b7 [Fintype K] [∀ k, Fintype (ι k)] [IsNoetherianRing R]
    (P : Ideal (NumbersDVR.MRing ι R)) (f : NumbersDVR.MRing ι R) (W : Ideal (NumbersDVR.MRing ι R)) :
    NumbersDVR.divCycle P f W = (ReciprocityTheory.ChartRestriction.G.Geo.divCycle (R := R) P f W : ℤ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Bridge».«divCycle_eq» := P2M_GroundTheory_Heights__Heights_Bridge_divCycle_eq_e8d03d8e52b7
