-- Prove2me | Theorems.Thm_PrimePairSieve_reciprocal_mass_table_1300000_2
-- name    : PrimePairSieve.reciprocal_mass_table_1300000_2
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T22:32:42.837224+00:00
-- url     : https://prove2.me/theorems/1ec05608-c23d-4239-9241-8e3b40a893c5
-- title:
--   Certified sieve-weight masses on [6485,9649]
-- statement:
--   For the literal squarefree sieve weight $w$ of the registered reciprocal threshold, this certificate verifies 20 specified interval masses within [6485,9649]. For each listed triple $(a,b,M)$,
--
--   $$M/10^8\le\sum_{a\le n\le b}w(n).$$
--
--   The exact triples appear in the formal statement. The proof checks 1,927 selected rows, 964 distinct prime certificates, their factorizations, exact weights, index bounds, strict ordering, and downward-rounded integer masses. Omitted nonnegative weights are permitted. The selected-weight cutoff $1/16000$ is a generator choice and is not a trusted hypothesis.
--
--   These masses can be reused at later reciprocal endpoints after checking disjointness and containment. This result alone does not assert the reciprocal threshold on this interval. Source: the finite-subset mass certificate derived from [the accepted batch soundness theorem](https://prove2.me/theorems/ad4bcc2f-0185-49a3-a4b5-1f232307b1c2), for [the registered reciprocal threshold](https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b). This is a formal computational certificate, not a new analytic estimate.
-- source:
--   Finite certificate for https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b; exact argument and scope in the statement.

import Definitions.Def_PrimePairSieve_ReciprocalMass
open scoped BigOperators
set_option autoImplicit false

theorem PrimePairSieve.reciprocal_mass_table_1300000_2 :
    PrimePairSieve.ReciprocalMass.Valid 100000000 {⟨6485,6614,20362614⟩,
⟨6615,6747,19505955⟩,
⟨6748,6882,18296456⟩,
⟨6883,7020,15928801⟩,
⟨7021,7161,16570568⟩,
⟨7162,7305,18030278⟩,
⟨7306,7452,18292200⟩,
⟨7453,7602,21116859⟩,
⟨7603,7755,17951522⟩,
⟨7756,7911,20563794⟩,
⟨7912,8070,16837218⟩,
⟨8071,8232,15959415⟩,
⟨8233,8397,18933892⟩,
⟨8398,8565,16779314⟩,
⟨8566,8737,17132062⟩,
⟨8738,8912,19915489⟩,
⟨8913,9091,18669515⟩,
⟨9092,9273,17586303⟩,
⟨9274,9459,18178495⟩,
⟨9460,9649,17920228⟩} := by sorry
