-- Prove2me | Theorems.Thm_PrimePairSieve_reciprocal_mass_table_50000_3
-- name    : PrimePairSieve.reciprocal_mass_table_50000_3
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T21:21:07.409772+00:00
-- url     : https://prove2.me/theorems/89422b5c-f8db-4b41-b019-30ed99023e52
-- title:
--   Certified sieve-weight masses on [21763,48086]
-- statement:
--   For the literal squarefree sieve weight $w$ of the registered reciprocal threshold, this certificate verifies 40 specified interval masses within [21763,48086]. For each listed triple $(a,b,M)$,
--
--   $$M/10^8\le\sum_{a\le n\le b}w(n).$$
--
--   The exact triples appear in the formal statement. The proof checks 1,965 selected rows, 430 distinct prime certificates, their factorizations, exact weights, index bounds, strict ordering, and downward-rounded integer masses. Omitted nonnegative weights are permitted. The selected-weight cutoff $1/1000$ is a generator choice and is not a trusted hypothesis.
--
--   These masses can be reused at later reciprocal endpoints after checking disjointness and containment. This result alone does not assert the reciprocal threshold on this interval. Source: the finite-subset mass certificate derived from [the accepted batch soundness theorem](https://prove2.me/theorems/ad4bcc2f-0185-49a3-a4b5-1f232307b1c2), for [the registered reciprocal threshold](https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b). This is a formal computational certificate, not a new analytic estimate.
-- source:
--   Finite certificate for https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b; exact argument and scope in the statement.

import Definitions.Def_PrimePairSieve_ReciprocalMass
open scoped BigOperators
set_option autoImplicit false

theorem PrimePairSieve.reciprocal_mass_table_50000_3 :
    PrimePairSieve.ReciprocalMass.Valid 100000000 {⟨21763,22198,15502443⟩,
⟨22199,22642,11817603⟩,
⟨22643,23095,13272728⟩,
⟨23096,23557,14479708⟩,
⟨23558,24029,12927965⟩,
⟨24030,24510,12880237⟩,
⟨24511,25001,12031392⟩,
⟨25002,25502,10798238⟩,
⟨25503,26013,12752015⟩,
⟨26014,26534,11665555⟩,
⟨26535,27065,11623121⟩,
⟨27066,27607,11637758⟩,
⟨27608,28160,9249465⟩,
⟨28161,28724,11649329⟩,
⟨28725,29299,10809332⟩,
⟨29300,29886,10392179⟩,
⟨29887,30484,10470060⟩,
⟨30485,31094,9961528⟩,
⟨31095,31716,10384076⟩,
⟨31717,32351,10228484⟩,
⟨32352,32999,10128822⟩,
⟨33000,33660,10289116⟩,
⟨33661,34334,9707269⟩,
⟨34335,35021,9503080⟩,
⟨35022,35722,8907570⟩,
⟨35723,36437,10634748⟩,
⟨36438,37166,9869539⟩,
⟨37167,37910,9989182⟩,
⟨37911,38669,9920614⟩,
⟨38670,39443,10378945⟩,
⟨39444,40232,9208655⟩,
⟨40233,41037,8493363⟩,
⟨41038,41858,9917229⟩,
⟨41859,42696,8626333⟩,
⟨42697,43550,8278494⟩,
⟨43551,44422,10409475⟩,
⟨44423,45311,8166981⟩,
⟨45312,46218,9878170⟩,
⟨46219,47143,10682238⟩,
⟨47144,48086,8039648⟩} := by sorry
