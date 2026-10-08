-- Prove2me | Theorems.Thm_PrimePairSieve_reciprocal_mass_table_50000_2
-- name    : PrimePairSieve.reciprocal_mass_table_50000_2
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T21:20:57.036285+00:00
-- url     : https://prove2.me/theorems/384f50a3-788b-450b-9743-ea224b97bdf6
-- title:
--   Certified sieve-weight masses on [9844,21762]
-- statement:
--   For the literal squarefree sieve weight $w$ of the registered reciprocal threshold, this certificate verifies 40 specified interval masses within [9844,21762]. For each listed triple $(a,b,M)$,
--
--   $$M/10^8\le\sum_{a\le n\le b}w(n).$$
--
--   The exact triples appear in the formal statement. The proof checks 1,973 selected rows, 521 distinct prime certificates, their factorizations, exact weights, index bounds, strict ordering, and downward-rounded integer masses. Omitted nonnegative weights are permitted. The selected-weight cutoff $1/1000$ is a generator choice and is not a trusted hypothesis.
--
--   These masses can be reused at later reciprocal endpoints after checking disjointness and containment. This result alone does not assert the reciprocal threshold on this interval. Source: the finite-subset mass certificate derived from [the accepted batch soundness theorem](https://prove2.me/theorems/ad4bcc2f-0185-49a3-a4b5-1f232307b1c2), for [the registered reciprocal threshold](https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b). This is a formal computational certificate, not a new analytic estimate.
-- source:
--   Finite certificate for https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b; exact argument and scope in the statement.

import Definitions.Def_PrimePairSieve_ReciprocalMass
open scoped BigOperators
set_option autoImplicit false

theorem PrimePairSieve.reciprocal_mass_table_50000_2 :
    PrimePairSieve.ReciprocalMass.Valid 100000000 {⟨9844,10040,16388420⟩,
⟨10041,10241,15836908⟩,
⟨10242,10446,14363459⟩,
⟨10447,10655,15890404⟩,
⟨10656,10869,14281363⟩,
⟨10870,11087,14119172⟩,
⟨11088,11309,13846058⟩,
⟨11310,11536,16085592⟩,
⟨11537,11767,14912868⟩,
⟨11768,12003,13966384⟩,
⟨12004,12244,13646608⟩,
⟨12245,12489,14278359⟩,
⟨12490,12739,12305400⟩,
⟨12740,12994,13965484⟩,
⟨12995,13254,14785236⟩,
⟨13255,13520,13730706⟩,
⟨13521,13791,13879404⟩,
⟨13792,14067,11486066⟩,
⟨14068,14349,15029585⟩,
⟨14350,14637,14062158⟩,
⟨14638,14930,12868169⟩,
⟨14931,15229,14344681⟩,
⟨15230,15534,14960794⟩,
⟨15535,15845,12464508⟩,
⟨15846,16162,12546661⟩,
⟨16163,16486,13264998⟩,
⟨16487,16816,13964273⟩,
⟨16817,17153,13204857⟩,
⟨17154,17497,13872494⟩,
⟨17498,17847,13009167⟩,
⟨17848,18204,12313630⟩,
⟨18205,18569,13377370⟩,
⟨18570,18941,14554702⟩,
⟨18942,19320,11442008⟩,
⟨19321,19707,14576106⟩,
⟨19708,20102,12475340⟩,
⟨20103,20505,13986952⟩,
⟨20506,20916,13005358⟩,
⟨20917,21335,13906836⟩,
⟨21336,21762,12425756⟩} := by sorry
