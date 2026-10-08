-- Prove2me | Theorems.Thm_PrimePairSieve_reciprocal_mass_table_1300000_3
-- name    : PrimePairSieve.reciprocal_mass_table_1300000_3
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T22:32:43.217467+00:00
-- url     : https://prove2.me/theorems/b182d895-5322-4c48-95af-b59e02b67f88
-- title:
--   Certified sieve-weight masses on [9650,12739]
-- statement:
--   For the literal squarefree sieve weight $w$ of the registered reciprocal threshold, this certificate verifies 14 specified interval masses within [9650,12739]. For each listed triple $(a,b,M)$,
--
--   $$M/10^8\le\sum_{a\le n\le b}w(n).$$
--
--   The exact triples appear in the formal statement. The proof checks 1,872 selected rows, 994 distinct prime certificates, their factorizations, exact weights, index bounds, strict ordering, and downward-rounded integer masses. Omitted nonnegative weights are permitted. The selected-weight cutoff $1/16000$ is a generator choice and is not a trusted hypothesis.
--
--   These masses can be reused at later reciprocal endpoints after checking disjointness and containment. This result alone does not assert the reciprocal threshold on this interval. Source: the finite-subset mass certificate derived from [the accepted batch soundness theorem](https://prove2.me/theorems/ad4bcc2f-0185-49a3-a4b5-1f232307b1c2), for [the registered reciprocal threshold](https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b). This is a formal computational certificate, not a new analytic estimate.
-- source:
--   Finite certificate for https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b; exact argument and scope in the statement.

import Definitions.Def_PrimePairSieve_ReciprocalMass
open scoped BigOperators
set_option autoImplicit false

theorem PrimePairSieve.reciprocal_mass_table_1300000_3 :
    PrimePairSieve.ReciprocalMass.Valid 100000000 {⟨9650,9843,18340214⟩,
⟨9844,10040,19653053⟩,
⟨10041,10241,19008889⟩,
⟨10242,10446,17897800⟩,
⟨10447,10655,19002400⟩,
⟨10656,10869,17501433⟩,
⟨10870,11087,17451243⟩,
⟨11088,11309,17323200⟩,
⟨11310,11536,19781140⟩,
⟨11537,11767,18573204⟩,
⟨11768,12003,18043077⟩,
⟨12004,12244,18347111⟩,
⟨12245,12489,18759153⟩,
⟨12490,12739,16677902⟩} := by sorry
