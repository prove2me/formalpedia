-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_ringKrullDim_quotient_eq_quotient_comap_of_isIntegral
-- name    : ReciprocityTheory.CA.ringKrullDim_quotient_eq_quotient_comap_of_isIntegral
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:16:30.533068+00:00
-- url     : https://prove2.me/theorems/2a8e1b1d-5e89-407a-a40c-07b48995b3f9
-- title:
--   CA: ring Krull Dim quotient eq quotient comap of is Integral
-- statement:
--   The CA construction uses the ring Krull Dim quotient eq quotient comap of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/SaturatedChains/Integral.lean#L81-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/SaturatedChains/Integral.lean#L81-L88

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_IsSaturatedChain
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA

theorem ReciprocityTheory.CA.ringKrullDim_quotient_eq_quotient_comap_of_isIntegral {A B : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [Algebra.IsIntegral A B] (I : Ideal B) :
    ringKrullDim (B ⧸ I) = ringKrullDim (A ⧸ I.comap (algebraMap A B)) := by sorry
