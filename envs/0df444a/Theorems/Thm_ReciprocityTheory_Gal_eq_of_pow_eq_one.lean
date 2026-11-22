-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_eq_of_pow_eq_one
-- name    : ReciprocityTheory.Gal.eq_of_pow_eq_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T16:49:01.108949+00:00
-- url     : https://prove2.me/theorems/63f16ab7-9f80-4b16-9c8c-1904d4410867
-- title:
--   Gal: eq of pow eq one
-- statement:
--   The Gal construction uses the eq of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/GlobalA.lean#L91-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/GlobalA.lean#L91-L106

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Pointwise
open ReciprocityTheory ReciprocityTheory.Gal
variable {Ω : Type*} [Field Ω]

theorem ReciprocityTheory.Gal.eq_of_pow_eq_one (A : ValuationSubring Ω) {N : ℕ} (hN : ¬ A.valuation (N : Ω) < 1)
    {a b : Ω} (ha : a ^ N = 1) (hb : b ^ N = 1) (h : A.valuation (a - b) < 1) : a = b := by sorry
