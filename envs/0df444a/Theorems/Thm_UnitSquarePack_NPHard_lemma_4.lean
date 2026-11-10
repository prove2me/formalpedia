-- Prove2me | Theorems.Thm_UnitSquarePack_NPHard_lemma_4
-- name    : UnitSquarePack.NPHard.lemma_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:20:24.340342+00:00
-- url     : https://prove2.me/theorems/1ef9a326-34d8-4167-8755-a76a587bf4b7
-- title:
--   Lemma 4 — Monotone-Planar-3SAT is NP-complete
-- statement:
--   **Monotone-Planar-3SAT** asks, for a monotone 3SAT formula $F$ (each clause has one to three literals, all positive or all negative) over at least three variables $x_0, \dots, x_{n-1}$, whether $F$ is satisfiable, where the instance comes with a plane drawing of the graph $G$ formed by the variable–clause incidences and the cycle $C = x_0x_1\cdots x_{n-1}x_0$ in which $C$ separates the positive from the negative clauses. The language consists of the binary codes of the instances whose graph admits such a drawing and whose formula is satisfiable.
--
--   **Lemma 4 (de Berg and Khosravi).** Monotone-Planar-3SAT is NP-complete:
--   $$\texttt{monotonePlanar3SAT} \in \mathrm{NP} \quad\text{and}\quad L \le_p \texttt{monotonePlanar3SAT} \ \text{ for every } L \in \mathrm{NP}.$$
--
--   The paper quotes this result from de Berg and Khosravi; it is the source problem of the reduction to Monotone-Layered-Planar-3SAT (Lemma 20) and so the root of the chain of reductions behind Theorem 1. NP and $\le_p$ are those of the published `CookPvsNP` (polynomial-time Turing machines, polynomial-time many-one reductions).
--
--   Differences from the source:
--   - reading: an instance Φ = (F, G) with a plane graph G in which C separates the positive from the negative clauses → the code of (n, F); the language requires that G, which F determines, has some crossing-free drawing in which C separates the positive from the negative clauses; reason: G's vertices and edges are fixed by F and the variable order; the embedding enters only through its existence, as in the published Planar-3SAT language KingTerrain_NPHard_PlanarSAT
--   - reading: 3SAT clauses (at most three literals, p. 20) → every clause has one, two or three literals on x_0, …, x_{n−1}; reason: a clause is a disjunction of literals; Figure 23's caption fixes at most three
--   - encoding: C separates all positive clauses from all negative clauses → no positive clause point lies in the connected component of ℝ² minus the image of C that contains a negative clause point; reason: this is what separation by a closed curve means in the drawing
--   - encoding: variables x_1, …, x_k; NP-complete → variables x_0, …, x_{n−1}; CookPvsNP.NPComplete over the alphabet Bool; reason: 0-based indices; the published Turing-machine notion of NP-completeness
--   - encoding: the cycle C through all variable vertices → 3 ≤ n; reason: a simple cycle has at least three vertices; n = 0, 1, 2 must not be interpreted as an empty curve or a single segment
-- source:
--   Abrahamsen and Stade, Hardness of Packing, Covering and Partitioning Simple Polygons with Unit Squares, arXiv:2404.09835v2, p. 4, Lemma 4

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_UnitSquarePack_NPHard_MonotonePlanar3SAT

set_option autoImplicit false

namespace UnitSquarePack.NPHard

/-- Lemma 4: Monotone-Planar-3SAT is NP-complete. -/
theorem lemma_4 : CookPvsNP.NPComplete monotonePlanar3SAT := by sorry

end UnitSquarePack.NPHard
