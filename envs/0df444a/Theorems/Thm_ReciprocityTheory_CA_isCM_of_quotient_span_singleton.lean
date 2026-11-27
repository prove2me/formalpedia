-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_isCM_of_quotient_span_singleton
-- name    : ReciprocityTheory.CA.isCM_of_quotient_span_singleton
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:02:55.159652+00:00
-- url     : https://prove2.me/theorems/994db57a-9204-4bc6-ace3-6f8743cf9083
-- title:
--   CA: is CM of quotient span singleton
-- statement:
--   The CA construction uses the is CM of quotient span singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/RingKrullDimQuotientOfMemAssociatedPrimes.lean#L45-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/RingKrullDimQuotientOfMemAssociatedPrimes.lean#L45-L49

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

theorem ReciprocityTheory.CA.isCM_of_quotient_span_singleton [IsNoetherianRing R] {x : R} (hx : x ∈ maximalIdeal R)
    (reg : x ∈ nonZeroDivisors R) [IsLocalRing (R ⧸ Ideal.span {x})]
    (h : IsCM (R ⧸ Ideal.span {x})) : IsCM R := by sorry
