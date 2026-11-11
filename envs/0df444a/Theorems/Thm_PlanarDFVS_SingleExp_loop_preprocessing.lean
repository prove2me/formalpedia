-- Prove2me | Theorems.Thm_PlanarDFVS_SingleExp_loop_preprocessing
-- name    : PlanarDFVS.SingleExp.loop_preprocessing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:42.352818+00:00
-- url     : https://prove2.me/theorems/694facc8-e0b8-4b83-9157-e393b5e98ebc
-- title:
--   Observation 2.1 — forced loop vertices and canonical support
-- statement:
--   Let $D$ be any finite directed multigraph and let $B$ be its set of loop vertices. Every DFVS contains $B$. With budget $k\in\mathbb N$,
--
--   $$\exists X\text{ DFVS},\ |X|\le k\quad\Longleftrightarrow\quad |B|\le k\ \land\ \exists Y\subseteq V\setminus B,\ |Y|\le k-|B|,\ D-(B\cup Y)\text{ acyclic}.$$
--
--   Thus insufficient budget is rejected before subtraction is used. The item also explicitly states that, for every retained vertex set, acyclicity of the multigraph is equivalent to acyclicity of its directed support matrix, using cyclic vertex sequences. This is the encoding obligation for the canonical algorithm input. Zero budget, empty graphs and arbitrarily many loop copies are included.
--
--   Differences from the source:
--   - encoding: finite vertex and arc sets with corner incidences → Fin n vertices, Fin m arc identities and paired incidence darts; closed walks define cycles; reason: finite relabeling retains loops, parallel arcs and repeated facial incidences; a nonempty closed directed walk contains a directed cycle
--   - reading: n is the number of vertices; digraphs may have arbitrarily many duplicate arcs → DFVS input is n, binary k and the n by n directed support bits, including loops; reason: all multigraph instances have the same cycle and DFVS answers as their support; explicit duplicate-list reading has an additional reading cost and is not claimed here
--   - encoding: delete loops and reduce the budget; reject a negative remainder → a conjunction first requires the loop count at most k, followed by natural residual subtraction; reason: the guard makes truncated subtraction agree exactly with the nonnegative residual budget
-- source:
--   Daniel Lokshtanov, Saket Saurabh, Jie Xue, STOC 2027 submission #1569 (October 2026), p. 5 (PDF p. 5), Observation 2.1 and §2

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Interfaces

open scoped BigOperators
open Classical

namespace PlanarDFVS.SingleExp

theorem loop_preprocessing :
    (∀ (n m : ℕ) (G : Graph n m) (A : Finset (Fin n)),
      InducedAcyclic G A ↔ SupportAcyclic (support G) A) ∧
    (∀ (n m : ℕ) (G : Graph n m),
      (∀ X : Finset (Fin n), IsDFVS G X → loopVertices G ⊆ X) ∧
      ∀ k : ℕ, Feasible G k ↔
        (loopVertices G).card ≤ k ∧
        ∃ Y : Finset (Fin n), Y ⊆ Finset.univ \ loopVertices G ∧
          Y.card ≤ k - (loopVertices G).card ∧
          InducedAcyclic G ((Finset.univ \ loopVertices G) \ Y)) := by sorry

end PlanarDFVS.SingleExp
