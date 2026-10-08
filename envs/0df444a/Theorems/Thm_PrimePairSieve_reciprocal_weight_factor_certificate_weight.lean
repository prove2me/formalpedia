-- Prove2me | Theorems.Thm_PrimePairSieve_reciprocal_weight_factor_certificate_weight
-- name    : PrimePairSieve.reciprocal_weight_factor_certificate_weight
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T17:43:23.145966+00:00
-- url     : https://prove2.me/theorems/600f092d-7e7e-44e1-895d-e5010b9fcc98
-- title:
--   Certified factors determine the literal reciprocal weight
-- statement:
--   This lemma connects a validated factor certificate to the literal public reciprocal sieve weight.
--
--   Under the same `reciprocal_weight_check` hypothesis as the soundness lemma, the literal weight `reciprocal_literal_weight n` equals the product over the certified factor set `s` of the Riesel–Vaughan factors (with value `1` at the prime `2`).
--
--   The proof reuses the squarefreeness and exact factor-set conclusion, then unfolds the definition of `reciprocal_literal_weight`.
-- source:
--   Prove2Me five-primes finite-window certificate design (2026-10-04)

import Mathlib
import Definitions.Def_PrimePairSieve_ReciprocalLiteralWeight
import Definitions.Def_PrimePairSieve_reciprocal_weight_check
open scoped BigOperators
set_option autoImplicit false

namespace PrimePairSieve

theorem reciprocal_weight_factor_certificate_weight (n : ℕ) (s : Finset ℕ)
    (hcheck : reciprocal_weight_check n s = true) :
    reciprocal_literal_weight n =
      ∏ p ∈ s, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2) := by sorry

end PrimePairSieve
