-- Prove2me | Theorems.Thm_PrimePairSieve_reciprocal_mass_table_1300000_5
-- name    : PrimePairSieve.reciprocal_mass_table_1300000_5
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T22:32:50.195993+00:00
-- url     : https://prove2.me/theorems/65b2ca1f-df04-48b0-8151-0f3457835a19
-- title:
--   Certified sieve-weight masses on [15846,18941]
-- statement:
--   For the literal squarefree sieve weight $w$ of the registered reciprocal threshold, this certificate verifies 9 specified interval masses within [15846,18941]. For each listed triple $(a,b,M)$,
--
--   $$M/10^8\le\sum_{a\le n\le b}w(n).$$
--
--   The exact triples appear in the formal statement. The proof checks 1,882 selected rows, 1,078 distinct prime certificates, their factorizations, exact weights, index bounds, strict ordering, and downward-rounded integer masses. Omitted nonnegative weights are permitted. The selected-weight cutoff $1/16000$ is a generator choice and is not a trusted hypothesis.
--
--   These masses can be reused at later reciprocal endpoints after checking disjointness and containment. This result alone does not assert the reciprocal threshold on this interval. Source: the finite-subset mass certificate derived from [the accepted batch soundness theorem](https://prove2.me/theorems/ad4bcc2f-0185-49a3-a4b5-1f232307b1c2), for [the registered reciprocal threshold](https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b). This is a formal computational certificate, not a new analytic estimate.
-- source:
--   Finite certificate for https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b; exact argument and scope in the statement.

import Definitions.Def_PrimePairSieve_ReciprocalMass
open scoped BigOperators
set_option autoImplicit false

theorem PrimePairSieve.reciprocal_mass_table_1300000_5 :
    PrimePairSieve.ReciprocalMass.Valid 100000000 {⟨15846,16162,17892138⟩,
⟨16163,16486,19275487⟩,
⟨16487,16816,19858790⟩,
⟨16817,17153,19328552⟩,
⟨17154,17497,19573308⟩,
⟨17498,17847,18831158⟩,
⟨17848,18204,18136247⟩,
⟨18205,18569,19169056⟩,
⟨18570,18941,20471601⟩} := by sorry
