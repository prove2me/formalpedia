-- Prove2me | Theorems.Thm_PrimePairSieve_reciprocal_mass_table_1300000_61
-- name    : PrimePairSieve.reciprocal_mass_table_1300000_61
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T22:57:17.641322+00:00
-- url     : https://prove2.me/theorems/daecfb83-7d9d-451c-a67a-3a406849de87
-- title:
--   Certified sieve-weight masses on [328422,334990]
-- statement:
--   For the literal squarefree sieve weight $w$ of the registered reciprocal threshold, this certificate verifies 1 specified interval masses within [328422,334990]. For each listed triple $(a,b,M)$,
--
--   $$M/10^8\le\sum_{a\le n\le b}w(n).$$
--
--   The exact triples appear in the formal statement. The proof checks 1,080 selected rows, 694 distinct prime certificates, their factorizations, exact weights, index bounds, strict ordering, and downward-rounded integer masses. Omitted nonnegative weights are permitted. The selected-weight cutoff $1/16000$ is a generator choice and is not a trusted hypothesis.
--
--   These masses can be reused at later reciprocal endpoints after checking disjointness and containment. This result alone does not assert the reciprocal threshold on this interval. Source: the finite-subset mass certificate derived from [the accepted batch soundness theorem](https://prove2.me/theorems/ad4bcc2f-0185-49a3-a4b5-1f232307b1c2), for [the registered reciprocal threshold](https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b). This is a formal computational certificate, not a new analytic estimate.
-- source:
--   Finite certificate for https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b; exact argument and scope in the statement.

import Definitions.Def_PrimePairSieve_ReciprocalMass
open scoped BigOperators
set_option autoImplicit false

theorem PrimePairSieve.reciprocal_mass_table_1300000_61 :
    PrimePairSieve.ReciprocalMass.Valid 100000000 {⟨328422,334990,17356555⟩} := by sorry
