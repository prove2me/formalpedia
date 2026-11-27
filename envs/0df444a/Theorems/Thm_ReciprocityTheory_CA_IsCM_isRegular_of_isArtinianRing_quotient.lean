-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_IsCM_isRegular_of_isArtinianRing_quotient
-- name    : ReciprocityTheory.CA.IsCM.isRegular_of_isArtinianRing_quotient
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:13:20.349232+00:00
-- url     : https://prove2.me/theorems/5c5f6dbb-858d-4e70-b1fc-8f4eb27e40f8
-- title:
--   Is CM: is Regular of is Artinian Ring quotient
-- statement:
--   The Is CM construction uses the is Regular of is Artinian Ring quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/RingKrullDimQuotientOfMemAssociatedPrimes.lean#L59-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/RingKrullDimQuotientOfMemAssociatedPrimes.lean#L59-L66

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Bridge
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Unmixed
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_RingKrullDimQuotientOfMemAssociatedPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence Pointwise
variable {R : Type*} [CommRing R] [IsLocalRing R]

theorem ReciprocityTheory.CA.IsCM.isRegular_of_isArtinianRing_quotient (h : IsCM R) (xs : List R)
    (hxs : ∀ r ∈ xs, r ∈ maximalIdeal R) (hlen : (xs.length : WithBot ℕ∞) = ringKrullDim R)
    (hart : IsArtinianRing (R ⧸ Ideal.ofList xs)) : IsRegular R xs := by sorry
