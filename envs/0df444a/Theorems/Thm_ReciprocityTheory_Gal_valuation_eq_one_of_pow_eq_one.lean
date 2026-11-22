-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_valuation_eq_one_of_pow_eq_one
-- name    : ReciprocityTheory.Gal.valuation_eq_one_of_pow_eq_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T16:49:07.539825+00:00
-- url     : https://prove2.me/theorems/86ea37ad-e46e-4c8c-a590-9c2e5b198909
-- title:
--   Gal: valuation eq one of pow eq one
-- statement:
--   The Gal construction uses the valuation eq one of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/GlobalA.lean#L73-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/GlobalA.lean#L73-L89

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

theorem ReciprocityTheory.Gal.valuation_eq_one_of_pow_eq_one (A : ValuationSubring Ω) {N : ℕ} (hN0 : N ≠ 0) {b : Ω}
    (hb : b ^ N = 1) : A.valuation b = 1 := by sorry
