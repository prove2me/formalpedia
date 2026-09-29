-- Prove2me | Theorems.Thm_TarchaBraids_exists_addStrand_hom
-- name    : TarchaBraids.exists_addStrand_hom
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T22:40:38.604738+00:00
-- url     : https://prove2.me/theorems/c75ecaf6-0f51-4702-9f14-91d98fd3f5f0
-- title:
--   Adding a strand carries half-twists to half-twists
-- statement:
--   Adding a strand to the right of all the others is a homomorphism of braid groups carrying each elementary half-twist to the half-twist of the same index.
--
--   Precisely, there is a group homomorphism $\pi_1(B_{0,n}E^2) \to \pi_1(B_{0,n+1}E^2)$ sending $[\mathrm{ht}_i]$ to $[\mathrm{ht}_i]$ for every $i$.
--
--   This is the bookkeeping half of the inductive step in Teorema 3.11. An induction on strand count for the generation of the braid group by half-twists has two parts: transporting the hypothesis for $n$ strands up to $n+1$, and handling the new generators contributed by the extra strand. This statement is the first part, and unlike the second it needs no missing topology.
--
--   The map is the one already used to split the Fadell--Neuwirth projection. Given a configuration, adjoin the point
--
--   $$z(p) \;=\; (n+1) + \sum_i \max\bigl(\operatorname{Re}p_i - n,\ 0\bigr),$$
--
--   which lies strictly to the right of every existing point. Two properties make it work here.
--
--   It descends to unordered configurations. The adjoined coordinate is a symmetric function of the points, so relabelling the configuration relabels the extended one by the same permutation with the new index fixed; the construction therefore passes to the quotient.
--
--   It carries half-twists to half-twists, and does so *on the nose* rather than up to homotopy. On a half-twist configuration every point has real part at most $n$: the two rotating points orbit the midpoint $i + \tfrac32$ at radius $\tfrac12$, so their real parts lie in $[i+1, i+2]$, and $i + 2 \le n$ because $i$ indexes a generator and so is at most $n-2$; the stationary points sit at integers $k+1 \le n$. Hence every term of the sum vanishes and $z(p) = n+1$ exactly. The extended configuration is then literally the half-twist configuration on $n+1$ strands at the same index, with the new strand parked at $n+1$. So the pushed-forward loop equals the target loop as a path, and no homotopy argument is needed.
--
--   The equality on the nose is what makes the statement cheap to use: the induced map on fundamental groups can be read off directly, with the base point preserved because $z$ evaluates to $n+1$ on the base configuration too.
-- source:
--   Tarcha, Braid Theory and the Artin Presentation, the inductive step of Teorema 3.11; cf. Birman, Braids, Links and Mapping Class Groups, Chapter 1.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

namespace TarchaBraids

open BraidsLinksMCG

theorem exists_addStrand_hom (n : ℕ) :
    ∃ f : GeomBraidGroup n →* GeomBraidGroup (n + 1),
      ∀ i : Fin (n - 1), f (halfTwistBraid n i)
        = halfTwistBraid (n + 1) (Fin.castLE (Nat.sub_le_sub_right (Nat.le_succ n) 1) i) := by
  sorry

end TarchaBraids
