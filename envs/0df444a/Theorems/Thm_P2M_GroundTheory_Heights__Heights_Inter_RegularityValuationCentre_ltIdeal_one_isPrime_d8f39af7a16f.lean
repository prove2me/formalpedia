-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularityValuationCentre_ltIdeal_one_isPrime_d8f39af7a16f
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RegularityValuationCentre_ltIdeal_one_isPrime_d8f39af7a16f
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:28:21.991955+00:00
-- url     : https://prove2.me/theorems/6730cf67-3932-4384-aea1-2ff59f582fa9
-- title:
--   P2 M Ground Theory Heights  Heights Inter Regularity Valuation Centre lt Ideal one is Prime d8f39af7a16f: P2 M Ground Theory Heights  Heights Inter Regularity Valuation Centre lt Ideal one is Prime d8
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Regularity Valuation Centre lt Ideal one is Prime d8f39af7a16f construction uses the P2 M Ground Theory Heights  Heights Inter Regularity Valuation Centre lt Ideal one is Prime d8f39af7a16f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/KerIsMultiHomogIdeal.lean#L18-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/KerIsMultiHomogIdeal.lean#L18-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsIntValuationLtOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_KerIsMultiHomogIdeal
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
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open GroundTheory.Heights₂.Heights.Inter.RegularityValuationCentre
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_RegularityValuationCentre_ltIdeal_one_isPrime_d8f39af7a16f {R Γ : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ] (v : Valuation R Γ) :
    (v.ltIdeal 1).IsPrime := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RegularityValuationCentre».«ltIdeal_one_isPrime» := P2M_GroundTheory_Heights__Heights_Inter_RegularityValuationCentre_ltIdeal_one_isPrime_d8f39af7a16f
