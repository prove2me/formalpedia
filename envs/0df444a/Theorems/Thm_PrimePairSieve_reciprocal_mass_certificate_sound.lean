-- Prove2me | Theorems.Thm_PrimePairSieve_reciprocal_mass_certificate_sound
-- name    : PrimePairSieve.reciprocal_mass_certificate_sound
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T21:20:31.707156+00:00
-- url     : https://prove2.me/theorems/b8b97115-24a5-4559-b407-f968afe2ca8d
-- title:
--   Soundness of squarefree sieve-weight mass tables
-- statement:
--   Let $S$ be a positive integer. Each finite certificate consists of a bucket $(a,b,M)$ and a strictly increasing list of positive indices $n$, each accompanied by distinct prime factors and exact integers $A_n,B_n>0$ representing its literal squarefree sieve weight $w(n)=A_n/B_n$. Assume every row passes the published factor-and-weight checker, every index lies in its bucket, and the claimed mass satisfies
--
--   $$M=\sum_{n\text{ selected}}\left\lfloor\frac{S A_n}{B_n}\right\rfloor.$$
--
--   Then each bucket has the certified mass lower bound
--
--   $$\frac M S\le\sum_{a\le n\le b}w(n).$$
--
--   Integer division rounds each selected weight downward, strict ordering excludes duplicates, and omitted weights are nonnegative. No completeness of the selected rows is assumed. Buckets may overlap in this theorem: a subsequent aggregation theorem requires disjointness before adding their bounds.
--
--   This packages the previously checked single-bucket mass argument into a reusable table certificate. The proof includes its factorization and rounding lemmas and imports only Mathlib and published definitions. It uses no unproved theorem mirror. The mathematical source is the finite-subset lower-bound argument of [the accepted batch checker](https://prove2.me/theorems/ad4bcc2f-0185-49a3-a4b5-1f232307b1c2), applied to the weight in [the original reciprocal threshold](https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b).
-- source:
--   Finite certificate for https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b; exact argument and scope in the statement.

import Definitions.Def_PrimePairSieve_ReciprocalMass
open scoped BigOperators
open PrimePairSieve
set_option autoImplicit false

theorem PrimePairSieve.reciprocal_mass_certificate_sound (scale : ℕ) (hs : 0 < scale)
    (certs : List (ReciprocalMass.Bucket × List ReciprocalBatch.Row))
    (hrows : (certs.flatMap Prod.snd).all ReciprocalBatch.rowCheck = true)
    (hchecks : certs.all (ReciprocalMass.massCheck scale) = true) :
    ReciprocalMass.Valid scale (certs.map Prod.fst).toFinset := by sorry
