-- Prove2me | Theorems.Thm_RemovingTrees_Main_small_cut_decomposition
-- name    : RemovingTrees.Main.small_cut_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T15:21:10.088496+00:00
-- url     : https://prove2.me/theorems/0775ab23-c2ce-4549-84f6-da328d999e57
-- title:
--   Lemma 3.8 — Efficient cover by at most 13 ε⁻² laminar families
-- statement:
--   Let $G'$ be a finite undirected multigraph on at least two vertices, containing $t\in\mathbb N$ edge-disjoint spanning trees, with
--   $$
--   0<\epsilon<\frac45,\qquad \lambda(G')\ge(2-\epsilon)t.
--   $$
--   Fix any root vertex $r$ and define
--   $$
--   \mathcal C=\{S\subseteq V\setminus\{r\}:|\delta_{G'}(S)|<t(2-3\epsilon/4)\}.
--   $$
--   A uniform polynomial-time exact-arithmetic machine, given the graph, packing, root, and real $\epsilon$, explicitly enumerates laminar families whose union equals $\mathcal C$, with their number $q$ satisfying $q\le13\epsilon^{-2}$.
--
--   This decomposition is the source's structural input for improving residual connectivity. No cover is supplied as a hypothesis. The case $t=0$ is retained: the strict threshold then makes $\mathcal C$ empty.
--
--   **Formalization Note** The active-edge input allows application to a residual subgraph. The output enumerates shores and families, and therefore supplies a polynomial-size enumeration. When $t>0$, the literal comprehension includes the empty shore, which the enumeration must also include.
--
--   Differences from the source:
--   - encoding: finite undirected multigraphs on at least two vertices → vertices Fin n with n ≥ 2 and individually labeled edges Fin m with symmetric endpoint cuts; reason: every source graph admits such labels; loops and parallel edges are retained
--   - encoding: a graph containing t packed spanning trees and an arbitrary root → an active-edge subset, an explicit witnessing packing, and a root identifier supplied to an exact-real machine; reason: all source graphs and roots are covered; supplying the packing exposes the proof input rather than assuming any decomposition
--   - encoding: efficient discovery for real ε → unit-cost exact arithmetic and sign comparisons on the supplied real parameter, with explicit cover output; reason: no rational restriction is imposed and no exponential shore list is given as input
-- source:
--   Nathan Klein, Neil Olver, Zi Song Yeoh, STOC 2027 submission #1092 (October 2026), Lemma 3.8, p.8

import Mathlib
import Definitions.Def_RemovingTrees_Main_GraphModel

set_option autoImplicit false

namespace RemovingTrees.Main

/-- Lemma 3.8, p.8, including t=0, the empty shore, the constant 13,
and actual enumeration of every family. No cover is supplied as an input. -/
theorem small_cut_decomposition :
    ∃ M : RealMachine, ∃ a d : ℕ, 0 < a ∧
    ∀ (n m : ℕ) (G : MultiGraph n m) (F : Finset (Fin m)) (t : ℕ)
      (ts : List (Finset (Fin m))) (root : Fin n) (ε : ℝ),
      2 ≤ n → Packing G F ts → ts.length = t →
      0 < ε → ε < (4:ℝ)/5 → CutLower G F ((2-ε)*t) →
      RealResult M a d
        (encGraph G ++ encSet F ++ encNat t ++ encNat root.val ++ encList encSet ts) [ε]
        (CoverOutput (rootedLowCuts G F root (t*((2:ℝ)-(3:ℝ)/4*ε))) ε) := by sorry
end RemovingTrees.Main
