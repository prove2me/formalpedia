-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_length_le_of_isRegular_of_mem_associatedPrimes
-- name    : ReciprocityTheory.CA.length_le_of_isRegular_of_mem_associatedPrimes
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:39:33.037166+00:00
-- url     : https://prove2.me/theorems/02993c18-d881-5a52-87a5-fcaccd6ec858
-- title:
--   CA: length le of is Regular of mem associated Primes
-- statement:
--   The CA construction uses the length le of is Regular of mem associated Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/AssDim.lean#L28-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/AssDim.lean#L28-L52

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ModDepthGE
import Definitions.Def_Lemmata_GeneralBFactRest_Imports
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_AssDim
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
variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

theorem ReciprocityTheory.CA.length_le_of_isRegular_of_mem_associatedPrimes : ∀ (rs : List R)
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M],
    (∀ r ∈ rs, r ∈ maximalIdeal R) → IsRegular M rs → ∀ {p : Ideal R},
    p ∈ associatedPrimes R M → (rs.length : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p)
  := by sorry
