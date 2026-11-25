-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_exists_ltSeries_lift_of_isIntegral
-- name    : ReciprocityTheory.CA.exists_ltSeries_lift_of_isIntegral
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:38:30.957388+00:00
-- url     : https://prove2.me/theorems/848c123d-df9c-4ec9-a373-7477d4762aac
-- title:
--   CA: exists lt Series lift of is Integral
-- statement:
--   The CA construction uses the exists lt Series lift of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/SaturatedChains/Integral.lean#L15-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/SaturatedChains/Integral.lean#L15-L57

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

theorem ReciprocityTheory.CA.exists_ltSeries_lift_of_isIntegral {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (h : Function.Injective (algebraMap A B))
    (l : LTSeries (PrimeSpectrum A)) :
    ∃ l' : LTSeries (PrimeSpectrum B), l'.length = l.length ∧
      l'.last.asIdeal.comap (algebraMap A B) = l.last.asIdeal := by sorry
