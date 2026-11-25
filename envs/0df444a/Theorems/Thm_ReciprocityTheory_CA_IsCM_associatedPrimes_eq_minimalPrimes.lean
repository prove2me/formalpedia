-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_IsCM_associatedPrimes_eq_minimalPrimes
-- name    : ReciprocityTheory.CA.IsCM.associatedPrimes_eq_minimalPrimes
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:58:21.919671+00:00
-- url     : https://prove2.me/theorems/8d1095de-621e-49fc-b89d-bf6a87ae1eb6
-- title:
--   Is CM: associated Primes eq minimal Primes
-- statement:
--   The Is CM construction uses the associated Primes eq minimal Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/RingKrullDimQuotientOfMemAssociatedPrimes.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/RingKrullDimQuotientOfMemAssociatedPrimes.lean#L34-L36

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Bridge
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Unmixed
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_RingKrullDimQuotientOfMemAssociatedPrimes
import Theorems.Thm_ReciprocityTheory_CA_IsCMMod_associatedPrimes_eq_minimalPrimes

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

theorem ReciprocityTheory.CA.IsCM.associatedPrimes_eq_minimalPrimes (h : IsCM R) :
    associatedPrimes R R = minimalPrimes R := by sorry
