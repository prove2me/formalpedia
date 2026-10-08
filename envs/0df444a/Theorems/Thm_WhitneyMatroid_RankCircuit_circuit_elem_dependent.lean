-- Prove2me | Theorems.Thm_WhitneyMatroid_RankCircuit_circuit_elem_dependent
-- name    : WhitneyMatroid.RankCircuit.circuit_elem_dependent
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:27:18.498224+00:00
-- url     : https://prove2.me/theorems/7f5015d5-2c1a-4a3a-8b1a-c4293284c739
-- title:
--   Lemma 5 — each element of a circuit is dependent on the rest of the circuit
-- statement:
--   Let $r$ be a rank function on the subsets of a finite set $M$ satisfying Whitney's postulates $(\mathrm R_1)$–$(\mathrm R_3)$, and let $P$ be a circuit of $r$, that is, a minimal set with positive nullity. Then for every element $e \in P$, $e$ is dependent on $P - e$:
--   $$r(P) = r(P - e).$$
--
--   This is the first step in reading off nullity from circuits; it underlies Theorem 4.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 512, Lemma 5

import Mathlib
import Definitions.Def_WhitneyMatroid_RankCircuit_IsRankSystem

namespace WhitneyMatroid.RankCircuit

theorem circuit_elem_dependent {α : Type*} [Fintype α] [DecidableEq α]
    (r : Finset α → ℤ) (hr : IsRankSystem r) (P : Finset α) (hP : circuitsOfRank r P)
    (e : α) (he : e ∈ P) :
    IsDependentOn r e (P.erase e) := by sorry

end WhitneyMatroid.RankCircuit
