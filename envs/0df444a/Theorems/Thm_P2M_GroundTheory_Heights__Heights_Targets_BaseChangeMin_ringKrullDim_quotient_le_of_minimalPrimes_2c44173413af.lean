-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_BaseChangeMin_ringKrullDim_quotient_le_of_minimalPrimes_2c44173413af
-- name    : P2M_GroundTheory_Heights__Heights_Targets_BaseChangeMin_ringKrullDim_quotient_le_of_minimalPrimes_2c44173413af
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:38.069045+00:00
-- url     : https://prove2.me/theorems/57c1e277-ba85-49b6-9298-d81d28afc037
-- title:
--   P2 M Ground Theory Heights  Heights Targets Base Change Min ring Krull Dim quotient le of minimal Primes 2c44173413af: P2 M Ground Theory Heights  Heights Targets Base Change Min ring Krull Dim quotie
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Base Change Min ring Krull Dim quotient le of minimal Primes 2c44173413af construction uses the P2 M Ground Theory Heights  Heights Targets Base Change Min ring Krull Dim quotient le of minimal Primes 2c44173413af property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/BaseChangeMinimal.lean#L89-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/BaseChangeMinimal.lean#L89-L110

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_BaseChangeMinimal
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

theorem P2M_GroundTheory_Heights__Heights_Targets_BaseChangeMin_ringKrullDim_quotient_le_of_minimalPrimes_2c44173413af {R : Type*} [CommRing R] (I : Ideal R)
    {N : WithBot ℕ∞} (h : ∀ Z ∈ I.minimalPrimes, ringKrullDim (R ⧸ Z) ≤ N) :
    ringKrullDim (R ⧸ I) ≤ N := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«BaseChangeMin».«ringKrullDim_quotient_le_of_minimalPrimes» := P2M_GroundTheory_Heights__Heights_Targets_BaseChangeMin_ringKrullDim_quotient_le_of_minimalPrimes_2c44173413af
