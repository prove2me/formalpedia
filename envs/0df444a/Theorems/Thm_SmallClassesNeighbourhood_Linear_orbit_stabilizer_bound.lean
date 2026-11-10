-- Prove2me | Theorems.Thm_SmallClassesNeighbourhood_Linear_orbit_stabilizer_bound
-- name    : SmallClassesNeighbourhood.Linear.orbit_stabilizer_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T16:35:57.951024+00:00
-- url     : https://prove2.me/theorems/ea33d26f-7839-47f0-88ba-c686c36eef0c
-- title:
--   Lemma 13 — orbit–stabiliser subset bound
-- statement:
--   Let a finite group H act on a finite set Γ, and let S_1,…,S_k be an ordered tuple of subsets of Γ. With its setwise stabilizer and tuple orbit as defined above,
--
--   $$|H|=|Orb_H(S_1,\ldots,S_k)|\,|H_{S_1,\ldots,S_k}|\le (2^k)^{|\Gamma|}|H_{S_1,\ldots,S_k}|.$$
--
--   The equality and inequality are both asserted. No injectivity of the action is assumed. This compares full automorphism groups with their explicitly named colour-preserving subgroups.
--
--   Differences from the source: none.
-- source:
--   John Sylvester, Viktor Zamaraev, Maksim Zhukovskii, STOC 2027 submission #1126 (October 2026), Lemma 13 (Orbit–stabiliser bound), printed p. 9 (PDF p. 10)

import Definitions.Def_SmallClassesNeighbourhood_Linear_groupActions

namespace SmallClassesNeighbourhood.Linear

theorem orbit_stabilizer_bound {H Γ : Type} [Group H] [Fintype H]
    [Fintype Γ] [DecidableEq Γ] [MulAction H Γ] (k : ℕ) (S : Fin k → Finset Γ) :
    Fintype.card H = (tupleOrbit (H := H) S).card * Nat.card (tupleStabilizer (H := H) S) ∧
    Fintype.card H ≤ (2 ^ k) ^ Fintype.card Γ * Nat.card (tupleStabilizer (H := H) S) := by sorry

end SmallClassesNeighbourhood.Linear
