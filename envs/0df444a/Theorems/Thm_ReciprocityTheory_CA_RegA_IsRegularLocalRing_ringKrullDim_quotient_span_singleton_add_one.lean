-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_RegA_IsRegularLocalRing_ringKrullDim_quotient_span_singleton_add_one
-- name    : ReciprocityTheory.CA.RegA.IsRegularLocalRing.ringKrullDim_quotient_span_singleton_add_one
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:38:30.931291+00:00
-- url     : https://prove2.me/theorems/c97535c6-aea8-52b7-a5bf-f06fdc16b98c
-- title:
--   Is Regular Local Ring: ring Krull Dim quotient span singleton add one
-- statement:
--   The Is Regular Local Ring construction uses the ring Krull Dim quotient span singleton add one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/RegGensA.lean#L284-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/RegGensA.lean#L284-L289

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_RegGensA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA ReciprocityTheory.CA.RegA
open ReciprocityTheory.CA.RegA.IsRegularLocalRing
open IsLocalRing
universe u

theorem ReciprocityTheory.CA.RegA.IsRegularLocalRing.ringKrullDim_quotient_span_singleton_add_one {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hx2 : x ∉ IsLocalRing.maximalIdeal R ^ 2) :
    ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 = ringKrullDim R := by sorry
