-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_IsCM_quotient_span_singleton
-- name    : ReciprocityTheory.CA.IsCM.quotient_span_singleton
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:38:44.928605+00:00
-- url     : https://prove2.me/theorems/5c3c68a5-2392-5878-af55-8791f4bfbc5e
-- title:
--   Is CM: quotient span singleton
-- statement:
--   The Is CM construction uses the quotient span singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/RingKrullDimQuotientOfMemAssociatedPrimes.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/RingKrullDimQuotientOfMemAssociatedPrimes.lean#L38-L43

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

theorem ReciprocityTheory.CA.IsCM.quotient_span_singleton (h : IsCM R) {x : R} (hx : x ∈ maximalIdeal R)
    (reg : x ∈ nonZeroDivisors R) [IsLocalRing (R ⧸ Ideal.span {x})] :
    IsCM (R ⧸ Ideal.span {x}) := by sorry
