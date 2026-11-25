-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_le_ringKrullDim_quotient_of_mem_associatedPrimes
-- name    : ReciprocityTheory.CA.ModDepthGE.le_ringKrullDim_quotient_of_mem_associatedPrimes
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:39:07.447799+00:00
-- url     : https://prove2.me/theorems/0d059801-17b2-5f76-8f0f-7c549b1617d9
-- title:
--   Mod Depth GE: le ring Krull Dim quotient of mem associated Primes
-- statement:
--   The Mod Depth GE construction uses the le ring Krull Dim quotient of mem associated Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/AssDim.lean#L56-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/AssDim.lean#L56-L61

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
variable {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]

theorem ReciprocityTheory.CA.ModDepthGE.le_ringKrullDim_quotient_of_mem_associatedPrimes {n : ℕ}
    (h : ModDepthGE R M n) {p : Ideal R} (hp : p ∈ associatedPrimes R M) :
    (n : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by sorry
