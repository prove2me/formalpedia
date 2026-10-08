-- Prove2me | Theorems.Thm_PrimePairSieve_reciprocal_mass_table_50000_1
-- name    : PrimePairSieve.reciprocal_mass_table_50000_1
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T21:20:55.914924+00:00
-- url     : https://prove2.me/theorems/beec37e3-930f-49e1-8724-f9e64a67aabc
-- title:
--   Certified sieve-weight masses on [3567,9843]
-- statement:
--   For the literal squarefree sieve weight $w$ of the registered reciprocal threshold, this certificate verifies 51 specified interval masses within [3567,9843]. For each listed triple $(a,b,M)$,
--
--   $$M/10^8\le\sum_{a\le n\le b}w(n).$$
--
--   The exact triples appear in the formal statement. The proof checks 1,998 selected rows, 462 distinct prime certificates, their factorizations, exact weights, index bounds, strict ordering, and downward-rounded integer masses. Omitted nonnegative weights are permitted. The selected-weight cutoff $1/1000$ is a generator choice and is not a trusted hypothesis.
--
--   These masses can be reused at later reciprocal endpoints after checking disjointness and containment. This result alone does not assert the reciprocal threshold on this interval. Source: the finite-subset mass certificate derived from [the accepted batch soundness theorem](https://prove2.me/theorems/ad4bcc2f-0185-49a3-a4b5-1f232307b1c2), for [the registered reciprocal threshold](https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b). This is a formal computational certificate, not a new analytic estimate.
-- source:
--   Finite certificate for https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b; exact argument and scope in the statement.

import Definitions.Def_PrimePairSieve_ReciprocalMass
open scoped BigOperators
set_option autoImplicit false

theorem PrimePairSieve.reciprocal_mass_table_50000_1 :
    PrimePairSieve.ReciprocalMass.Valid 100000000 {⟨3567,3638,18993982⟩,
⟨3639,3711,15012618⟩,
⟨3712,3786,14958202⟩,
⟨3787,3862,16129569⟩,
⟨3863,3940,18618842⟩,
⟨3941,4019,18193631⟩,
⟨4020,4100,15901928⟩,
⟨4101,4183,16508529⟩,
⟨4184,4267,13603285⟩,
⟨4268,4353,19563682⟩,
⟨4354,4441,15253971⟩,
⟨4442,4530,19502775⟩,
⟨4531,4621,11851175⟩,
⟨4622,4714,15358780⟩,
⟨4715,4809,15747708⟩,
⟨4810,4906,19868468⟩,
⟨4907,5005,15006873⟩,
⟨5006,5106,10617191⟩,
⟨5107,5209,16003486⟩,
⟨5210,5314,14970654⟩,
⟨5315,5421,13874869⟩,
⟨5422,5530,14821429⟩,
⟨5531,5641,14391141⟩,
⟨5642,5754,16756266⟩,
⟨5755,5870,14668172⟩,
⟨5871,5988,14213362⟩,
⟨5989,6108,20159647⟩,
⟨6109,6231,14279536⟩,
⟨6232,6356,17606815⟩,
⟨6357,6484,13232966⟩,
⟨6485,6614,18055183⟩,
⟨6615,6747,17364714⟩,
⟨6748,6882,16175316⟩,
⟨6883,7020,13843991⟩,
⟨7021,7161,13752498⟩,
⟨7162,7305,15318283⟩,
⟨7306,7452,15612973⟩,
⟨7453,7602,18999362⟩,
⟨7603,7755,15494690⟩,
⟨7756,7911,17851825⟩,
⟨7912,8070,14386302⟩,
⟨8071,8232,13621454⟩,
⟨8233,8397,16703990⟩,
⟨8398,8565,14117410⟩,
⟨8566,8737,14614623⟩,
⟨8738,8912,17175172⟩,
⟨8913,9091,15912949⟩,
⟨9092,9273,14473182⟩,
⟨9274,9459,15166685⟩,
⟨9460,9649,14993753⟩,
⟨9650,9843,15352565⟩} := by sorry
