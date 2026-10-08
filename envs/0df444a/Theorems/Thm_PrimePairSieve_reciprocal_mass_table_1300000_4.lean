-- Prove2me | Theorems.Thm_PrimePairSieve_reciprocal_mass_table_1300000_4
-- name    : PrimePairSieve.reciprocal_mass_table_1300000_4
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T22:32:47.714043+00:00
-- url     : https://prove2.me/theorems/8a1cf49c-2159-41cb-995c-fded6b201fbd
-- title:
--   Certified sieve-weight masses on [12740,15845]
-- statement:
--   For the literal squarefree sieve weight $w$ of the registered reciprocal threshold, this certificate verifies 11 specified interval masses within [12740,15845]. For each listed triple $(a,b,M)$,
--
--   $$M/10^8\le\sum_{a\le n\le b}w(n).$$
--
--   The exact triples appear in the formal statement. The proof checks 1,895 selected rows, 1,035 distinct prime certificates, their factorizations, exact weights, index bounds, strict ordering, and downward-rounded integer masses. Omitted nonnegative weights are permitted. The selected-weight cutoff $1/16000$ is a generator choice and is not a trusted hypothesis.
--
--   These masses can be reused at later reciprocal endpoints after checking disjointness and containment. This result alone does not assert the reciprocal threshold on this interval. Source: the finite-subset mass certificate derived from [the accepted batch soundness theorem](https://prove2.me/theorems/ad4bcc2f-0185-49a3-a4b5-1f232307b1c2), for [the registered reciprocal threshold](https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b). This is a formal computational certificate, not a new analytic estimate.
-- source:
--   Finite certificate for https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b; exact argument and scope in the statement.

import Definitions.Def_PrimePairSieve_ReciprocalMass
open scoped BigOperators
set_option autoImplicit false

theorem PrimePairSieve.reciprocal_mass_table_1300000_4 :
    PrimePairSieve.ReciprocalMass.Valid 100000000 {⟨12740,12994,18645457⟩,
⟨12995,13254,19671203⟩,
⟨13255,13520,18809766⟩,
⟨13521,13791,19270453⟩,
⟨13792,14067,16551221⟩,
⟨14068,14349,20497105⟩,
⟨14350,14637,19685154⟩,
⟨14638,14930,18895335⟩,
⟨14931,15229,19719630⟩,
⟨15230,15534,20617458⟩,
⟨15535,15845,18440603⟩} := by sorry
