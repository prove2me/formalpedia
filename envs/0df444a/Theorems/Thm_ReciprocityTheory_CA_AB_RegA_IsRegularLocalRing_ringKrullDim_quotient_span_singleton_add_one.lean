-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_AB_RegA_IsRegularLocalRing_ringKrullDim_quotient_span_singleton_add_one
-- name    : ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.ringKrullDim_quotient_span_singleton_add_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:03:05.684068+00:00
-- url     : https://prove2.me/theorems/5926e50b-e55c-497c-9181-b190d67397c5
-- title:
--   Is Regular Local Ring: ring Krull Dim quotient span singleton add one
-- statement:
--   The Is Regular Local Ring construction uses the ring Krull Dim quotient span singleton add one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/MaximalIdealSquares/RingKrullDimQuotientSpanSingletonAddOne.lean#L263-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/MaximalIdealSquares/RingKrullDimQuotientSpanSingletonAddOne.lean#L263-L268

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA ReciprocityTheory.CA.AB ReciprocityTheory.CA.AB.RegA
open ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing
open IsLocalRing
universe u

theorem ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.ringKrullDim_quotient_span_singleton_add_one {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hx2 : x ∉ IsLocalRing.maximalIdeal R ^ 2) :
    ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 = ringKrullDim R := by sorry
