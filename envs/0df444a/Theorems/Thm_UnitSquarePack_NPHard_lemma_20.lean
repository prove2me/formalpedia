-- Prove2me | Theorems.Thm_UnitSquarePack_NPHard_lemma_20
-- name    : UnitSquarePack.NPHard.lemma_20
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:20:15.964277+00:00
-- url     : https://prove2.me/theorems/9bc5ec5d-85c1-4d97-aa06-bb5fae2e60c1
-- title:
--   Lemma 20 — Monotone-Layered-Planar-3SAT is NP-hard
-- statement:
--   In **Monotone-Layered-Planar-3SAT** the input is a 3SAT formula (one to three literals per clause) together with a planar, integer-coordinate, straight-line embedding of its variable–clause incidence graph, with variables at even heights, clauses at odd heights, every edge joining adjacent heights, clauses at heights $4k+1$ positive and clauses at heights $4k-1$ negative. The question is whether the formula is satisfiable.
--
--   **Lemma 20.** Monotone-Layered-Planar-3SAT is NP-hard: every language in NP (over any finite nonempty alphabet) reduces to it by a polynomial-time many-one reduction,
--   $$\forall L \in \mathrm{NP}:\quad L \le_p \texttt{monotoneLayeredPlanar3SAT}.$$
--
--   This is the first step from Monotone-Planar-3SAT (Lemma 4) towards Monotone-Clover-3SAT (Lemma 21), the problem the packing reduction of Theorem 1 starts from.
--
--   Differences from the source:
--   - encoding: a planar, integer-coordinate straight line embedding of the incidence graph (part of the input) → vertex coordinates as binary integers in the code; planarity = distinct vertex points, no edge segment through another vertex, distinct edge segments meet only in a common endpoint; reason: the standard meaning of a planar straight-line embedding
--   - encoding: clause vertices with y coordinates of the form 4k − 1 are negative → y mod 4 = 3 (Lean's Euclidean remainder); reason: 4k − 1 ≡ 3 (mod 4) for every integer k, negative y included
--   - reading: an instance of 3SAT (at most three literals per clause, p. 20) → every clause has one, two or three literals on x_0, …, x_{n−1}; reason: Figure 23's caption fixes at most three; the edge splitting of the proof creates 2-literal clauses
--   - encoding: NP-hard → KingTerrain.NPHard.IsNPHard (every NP language over every finite nonempty alphabet is CookPvsNP.PolyReducible to it) on a language over Bool; reason: the published notion of NP-hardness
-- source:
--   Abrahamsen and Stade, Hardness of Packing, Covering and Partitioning Simple Polygons with Unit Squares, arXiv:2404.09835v2, p. 19, Lemma 20

import Mathlib
import Definitions.Def_KingTerrain_NPHard_Complexity
import Definitions.Def_UnitSquarePack_NPHard_MonotoneLayeredPlanar3SAT

set_option autoImplicit false

namespace UnitSquarePack.NPHard

/-- Lemma 20: Monotone-Layered-Planar-3SAT is NP-hard. -/
theorem lemma_20 : KingTerrain.NPHard.IsNPHard monotoneLayeredPlanar3SAT := by sorry

end UnitSquarePack.NPHard
