-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_BaseChangeMin_height_eq_of_mem_minimalPrimes_map_b3f5ffc662ee
-- name    : P2M_GroundTheory_Heights__Heights_Targets_BaseChangeMin_height_eq_of_mem_minimalPrimes_map_b3f5ffc662ee
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:39:30.440872+00:00
-- url     : https://prove2.me/theorems/088c45a6-1f53-5984-87d6-724c9d327810
-- title:
--   P2 M Ground Theory Heights  Heights Targets Base Change Min height eq of mem minimal Primes map b3f5ffc662ee: P2 M Ground Theory Heights  Heights Targets Base Change Min height eq of mem minimal Prime
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Base Change Min height eq of mem minimal Primes map b3f5ffc662ee construction uses the P2 M Ground Theory Heights  Heights Targets Base Change Min height eq of mem minimal Primes map b3f5ffc662ee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/BaseChangeMinimal.lean#L47-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/BaseChangeMinimal.lean#L47-L64

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_BaseChangeMinimal
import Theorems.Thm_ReciprocityTheory_AnForm_R_BaseChangeC_height_eq_of_mem_minimalPrimes_map

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
open MvPolynomial
open GroundTheory.Heights₂.Heights.Targets.BaseChangeMin
variable {σ : Type*} [Fintype σ] {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem P2M_GroundTheory_Heights__Heights_Targets_BaseChangeMin_height_eq_of_mem_minimalPrimes_map_b3f5ffc662ee (𝔭 : Ideal (MvPolynomial σ F)) [𝔭.IsPrime]
    (Q : Ideal (MvPolynomial σ F'))
    (hQ : Q ∈ (Ideal.map (MvPolynomial.map (algebraMap F F')) 𝔭).minimalPrimes) :
    Q.height = 𝔭.height := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«BaseChangeMin».«height_eq_of_mem_minimalPrimes_map» := P2M_GroundTheory_Heights__Heights_Targets_BaseChangeMin_height_eq_of_mem_minimalPrimes_map_b3f5ffc662ee
