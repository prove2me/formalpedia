-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_multAt_eq_toNat_f8855e745589
-- name    : P2M_GroundTheory_Heights__Heights_Bridge_multAt_eq_toNat_f8855e745589
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:59.590164+00:00
-- url     : https://prove2.me/theorems/f68e6d87-3d00-4641-af7f-58cc2e26ec4d
-- title:
--   P2 M Ground Theory Heights  Heights Bridge mult At eq to Nat f8855e745589: P2 M Ground Theory Heights  Heights Bridge mult At eq to Nat f8855e745589
-- statement:
--   The P2 M Ground Theory Heights  Heights Bridge mult At eq to Nat f8855e745589 construction uses the P2 M Ground Theory Heights  Heights Bridge mult At eq to Nat f8855e745589 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/IsMultiHomogIdealIff.lean#L88-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/IsMultiHomogIdealIff.lean#L88-L91

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

theorem P2M_GroundTheory_Heights__Heights_Bridge_multAt_eq_toNat_f8855e745589 (J W : Ideal (NumbersDVR.MRing ι R)) [W.IsPrime] :
    ReciprocityTheory.ChartRestriction.G.Geo.multAt (R := R) J W = (NumbersDVR.multAt J W).toNat := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Bridge».«multAt_eq_toNat» := P2M_GroundTheory_Heights__Heights_Bridge_multAt_eq_toNat_f8855e745589
