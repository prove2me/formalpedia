-- Prove2me | Theorems.Thm_PrimePairSieve_reciprocal_mass_endpoint_sound
-- name    : PrimePairSieve.reciprocal_mass_endpoint_sound
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T21:20:45.162149+00:00
-- url     : https://prove2.me/theorems/a499e496-ca5d-43a4-84a8-60610b3649cf
-- title:
--   Disjoint mass tables bound reciprocal sieve endpoints
-- statement:
--   Let $S,L$ be positive integers. Let a finite collection of buckets $(a_i,b_i,M_i)$ satisfy $a_i\ge1$, pairwise strict separation of their integer intervals, and
--
--   $$\frac{M_i}{S}\le\sum_{a_i\le n\le b_i}w(n),$$
--
--   where $w$ is the literal nonnegative squarefree prime-factor weight of the registered reciprocal threshold. Then
--
--   $$\frac1S\sum_{i:\ b_i\le L}\left\lfloor\frac{M_iL}{L+b_i}\right\rfloor
--   \le\sum_{1\le n\le L}\frac{w(n)}{1+n/L}.$$
--
--   On each included interval, $n\le b_i$ permits replacing its denominator by $1+b_i/L$. Integer division rounds the resulting contribution down. Strict separation prevents double counting; omitted intervals and unselected weights are harmless by nonnegativity. Positivity of the scale, endpoint, and lower indices is explicit. There is no implicit assumption that the buckets cover all indices.
--
--   This theorem permits reuse of verified masses at many later endpoints, reducing the repeated computation needed for [the original reciprocal threshold](https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b). It is an elementary finite-sum certificate theorem, not a new prime-distribution estimate. The submitted proof proves the general nonnegative-weight transfer internally and includes the literal weight's nonnegativity proof.
-- source:
--   Finite certificate for https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b; exact argument and scope in the statement.

import Definitions.Def_PrimePairSieve_ReciprocalMass
open scoped BigOperators
open PrimePairSieve
set_option autoImplicit false

theorem PrimePairSieve.reciprocal_mass_endpoint_sound (scale L : ℕ) (hs : 0 < scale) (hL : 0 < L)
    (buckets : Finset ReciprocalMass.Bucket)
    (hpositive : ∀ b ∈ buckets, 1 ≤ b.lower)
    (hdisjoint : ∀ a ∈ buckets, ∀ b ∈ buckets, a ≠ b →
      a.upper < b.lower ∨ b.upper < a.lower)
    (hmass : ReciprocalMass.Valid scale buckets) :
    (ReciprocalMass.endpointSum L buckets : ℝ) / scale ≤
      ∑ n ∈ Finset.Icc 1 L, ReciprocalBatch.weight n / (1 + (n : ℝ) / L) := by sorry
