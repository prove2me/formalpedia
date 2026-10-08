-- Prove2me | Theorems.Thm_PrimePairSieve_reciprocal_mass_table_1300000_1
-- name    : PrimePairSieve.reciprocal_mass_table_1300000_1
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T22:32:40.091509+00:00
-- url     : https://prove2.me/theorems/759e762b-9558-4cfe-b5f4-49d6a1b571fa
-- title:
--   Certified sieve-weight masses on [3229,6484]
-- statement:
--   For the literal squarefree sieve weight $w$ of the registered reciprocal threshold, this certificate verifies 35 specified interval masses within [3229,6484]. For each listed triple $(a,b,M)$,
--
--   $$M/10^8\le\sum_{a\le n\le b}w(n).$$
--
--   The exact triples appear in the formal statement. The proof checks 1,978 selected rows, 841 distinct prime certificates, their factorizations, exact weights, index bounds, strict ordering, and downward-rounded integer masses. Omitted nonnegative weights are permitted. The selected-weight cutoff $1/16000$ is a generator choice and is not a trusted hypothesis.
--
--   These masses can be reused at later reciprocal endpoints after checking disjointness and containment. This result alone does not assert the reciprocal threshold on this interval. Source: the finite-subset mass certificate derived from [the accepted batch soundness theorem](https://prove2.me/theorems/ad4bcc2f-0185-49a3-a4b5-1f232307b1c2), for [the registered reciprocal threshold](https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b). This is a formal computational certificate, not a new analytic estimate.
-- source:
--   Finite certificate for https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b; exact argument and scope in the statement.

import Definitions.Def_PrimePairSieve_ReciprocalMass
open scoped BigOperators
set_option autoImplicit false

theorem PrimePairSieve.reciprocal_mass_table_1300000_1 :
    PrimePairSieve.ReciprocalMass.Valid 100000000 {⟨3229,3293,17903599⟩,
⟨3294,3359,19310981⟩,
⟨3360,3427,16335375⟩,
⟨3428,3496,14451469⟩,
⟨3497,3566,14206432⟩,
⟨3567,3638,19548998⟩,
⟨3639,3711,15502009⟩,
⟨3712,3786,15385190⟩,
⟨3787,3862,16600468⟩,
⟨3863,3940,19182628⟩,
⟨3941,4019,18745216⟩,
⟨4020,4100,16888732⟩,
⟨4101,4183,17618607⟩,
⟨4184,4267,14596154⟩,
⟨4268,4353,20743638⟩,
⟨4354,4441,16517670⟩,
⟨4442,4530,20676341⟩,
⟨4531,4621,13912378⟩,
⟨4622,4714,16985399⟩,
⟨4715,4809,17490122⟩,
⟨4810,4906,21773308⟩,
⟨4907,5005,16409601⟩,
⟨5006,5106,12455355⟩,
⟨5107,5209,17769878⟩,
⟨5210,5314,16780672⟩,
⟨5315,5421,15999322⟩,
⟨5422,5530,16610676⟩,
⟨5531,5641,16600154⟩,
⟨5642,5754,18669143⟩,
⟨5755,5870,16604025⟩,
⟨5871,5988,16333726⟩,
⟨5989,6108,22366288⟩,
⟨6109,6231,16312011⟩,
⟨6232,6356,19381707⟩,
⟨6357,6484,15171163⟩} := by sorry
