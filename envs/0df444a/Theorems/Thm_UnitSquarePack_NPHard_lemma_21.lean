-- Prove2me | Theorems.Thm_UnitSquarePack_NPHard_lemma_21
-- name    : UnitSquarePack.NPHard.lemma_21
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:20:20.277915+00:00
-- url     : https://prove2.me/theorems/862f17e9-6838-483d-8be2-d1e298822dc1
-- title:
--   Lemma 21 — Monotone-Clover-3SAT is NP-hard
-- statement:
--   In **Monotone-Clover-3SAT** the input is a 3SAT formula over $x_0, \dots, x_{n-1}$ whose clauses come in two lists, positive clauses $c_0, \dots, c_{p-1}$ and negative clauses $d_0, \dots, d_{q-1}$ ($p, q \ge 1$), such that the clover graph (incidences, the three paths $x_0\cdots x_{n-1}$, $c_0\cdots c_{p-1}$, $d_0\cdots d_{q-1}$, and the edges $x_0c_0$, $c_0x_{n-1}$, $x_{n-1}d_0$, $d_0x_0$) is planar. The question is whether the formula is satisfiable.
--
--   **Lemma 21.** Monotone-Clover-3SAT is NP-hard:
--   $$\forall L \in \mathrm{NP}:\quad L \le_p \texttt{monotoneClover3SAT}.$$
--
--   Monotone-Clover-3SAT is the source problem of the reduction in the proof of Theorem 1 (§4.9): its schematics have an orthogonally convex shape (Lemma 22), which is what makes an orthogonally convex polygon possible.
--
--   Differences from the source:
--   - reading: clauses c_1, …, c_p and d_1, …, d_q → p ≥ 1 and q ≥ 1; reason: the definition names c_1 and d_1 in the edges (x_1, c_1), (c_1, x_n), (x_n, d_1), (d_1, x_1)
--   - reading: each clause d_i is negative (i.e., it is of form ¬x_j ∨ ¬x_k ∨ ¬v_ℓ) → every literal of every d_j is negative; reason: v_ℓ is a typo for x_ℓ (INSIGHTS I4); the instance has no variables named v
--   - reading: a planar embedding of the graph G (in the input) → the clover graph has a crossing-free drawing (WilliamsonShmoys.HasPlanarDrawingOn); the code carries the formula only; reason: the embedding is used only through its existence, as for Lemma 4
--   - reading: an instance of 3SAT (at most three literals per clause, p. 20) → every clause has one, two or three literals on x_0, …, x_{n−1}; reason: Figure 23's caption fixes at most three; the reduction of Lemma 20 creates 2-literal clauses
--   - encoding: variables x_1, …, x_n; NP-hard → x_0, …, x_{n−1}; KingTerrain.NPHard.IsNPHard on a language over Bool; reason: 0-based indices; the published notion of NP-hardness
-- source:
--   Abrahamsen and Stade, Hardness of Packing, Covering and Partitioning Simple Polygons with Unit Squares, arXiv:2404.09835v2, p. 20, Lemma 21

import Mathlib
import Definitions.Def_KingTerrain_NPHard_Complexity
import Definitions.Def_UnitSquarePack_NPHard_MonotoneClover3SAT

set_option autoImplicit false

namespace UnitSquarePack.NPHard

/-- Lemma 21: Monotone-Clover-3SAT is NP-hard. -/
theorem lemma_21 : KingTerrain.NPHard.IsNPHard monotoneClover3SAT := by sorry

end UnitSquarePack.NPHard
