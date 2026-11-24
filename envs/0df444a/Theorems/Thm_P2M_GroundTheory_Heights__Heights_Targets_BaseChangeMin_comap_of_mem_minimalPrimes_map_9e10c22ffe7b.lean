-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_BaseChangeMin_comap_of_mem_minimalPrimes_map_9e10c22ffe7b
-- name    : P2M_GroundTheory_Heights__Heights_Targets_BaseChangeMin_comap_of_mem_minimalPrimes_map_9e10c22ffe7b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:42.138887+00:00
-- url     : https://prove2.me/theorems/831880fc-c41a-45a6-b71e-8081ecf3bb67
-- title:
--   P2 M Ground Theory Heights  Heights Targets Base Change Min comap of mem minimal Primes map 9e10c22ffe7b: P2 M Ground Theory Heights  Heights Targets Base Change Min comap of mem minimal Primes map 9e
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Base Change Min comap of mem minimal Primes map 9e10c22ffe7b construction uses the P2 M Ground Theory Heights  Heights Targets Base Change Min comap of mem minimal Primes map 9e10c22ffe7b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/BaseChangeMinimal.lean#L27-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/BaseChangeMinimal.lean#L27-L45

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_BaseChangeMinimal
import Theorems.Thm_ReciprocityTheory_AnForm_R_BaseChangeC_comap_of_mem_minimalPrimes_map

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
omit [Fintype σ]

theorem P2M_GroundTheory_Heights__Heights_Targets_BaseChangeMin_comap_of_mem_minimalPrimes_map_9e10c22ffe7b (𝔭 : Ideal (MvPolynomial σ F)) [𝔭.IsPrime]
    (Q : Ideal (MvPolynomial σ F'))
    (hQ : Q ∈ (Ideal.map (MvPolynomial.map (algebraMap F F')) 𝔭).minimalPrimes) :
    Q.comap (MvPolynomial.map (algebraMap F F')) = 𝔭 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«BaseChangeMin».«comap_of_mem_minimalPrimes_map» := P2M_GroundTheory_Heights__Heights_Targets_BaseChangeMin_comap_of_mem_minimalPrimes_map_9e10c22ffe7b
