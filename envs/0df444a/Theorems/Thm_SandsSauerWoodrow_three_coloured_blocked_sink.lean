-- Prove2me | Theorems.Thm_SandsSauerWoodrow_three_coloured_blocked_sink
-- name    : SandsSauerWoodrow.three_coloured_blocked_sink
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-17T01:04:42.727672+00:00
-- url     : https://prove2.me/theorems/05e510c8-b1a9-458f-9129-6b0db3f265da
-- title:
--   Sands-Sauer-Woodrow Theorem 3: blocked three-coloured tournaments have a monochromatic sink
-- statement:
--   This is Theorem 3 of Sands, Sauer and Woodrow, *On monochromatic paths in edge-coloured digraphs*, J. Combin. Theory Ser. B **33** (1982), 271–275, stated on p. 274 with its proof on pp. 274–275.
--
--   Let $T$ be a tournament on a nonempty finite set $V$ of vertices whose arcs are coloured with three colours — call them red, blue and green, encoded as $0$, $1$ and $2$ — and suppose the vertices are partitioned into blocks, given by a map $b : V \to \iota$ whose fibres are the blocks, such that for every arc $u \to v$ of $T$:
--
--   1. if $u$ and $v$ lie in different blocks, $b(u) \neq b(v)$, then the arc is red; and
--   2. if $u$ and $v$ lie in the same block, $b(u) = b(v)$, then the arc is blue or green.
--
--   Then there is a vertex $v_0$ such that every other vertex $x \neq v_0$ reaches $v_0$ by a monochromatic directed path.
--
--   The source proves this from the two-coloured corollary, block by block.
--
--   **Formalization Note.** The map $b$ is required only to describe the partition; it need not be surjective, since the conclusion does not distinguish empty blocks. Colours are constrained on arcs only, and the colours are named in the order red $= 0$, blue $= 1$, green $= 2$ fixed by the encoding.
-- source:
--   B. Sands, N. Sauer, R. Woodrow, On monochromatic paths in edge-coloured digraphs, J. Combin. Theory Ser. B 33 (1982), no. 3, 271-275. Theorem 1 (pp. 271-273); Corollary 2 (p. 273); Theorem 3 (pp. 274-275); PROBLEM (p. 275).

import Definitions.Def_opg1808_colored_tournaments

open OPG1808

universe u v

namespace SandsSauerWoodrow

theorem three_coloured_blocked_sink {V : Type u} {ι : Type v} [Fintype V] [Nonempty V]
    (D : Digraph V) (color : ArcColoring V) (htournament : IsTournament D)
    (b : V → ι)
    (hred : ∀ u v, D u v → b u ≠ b v → color u v = 0)
    (hbg : ∀ u v, D u v → b u = b v → (color u v = 1 ∨ color u v = 2)) :
    ∃ v : V, ∀ x : V, x ≠ v → MonochromaticallyReaches D color x v := by sorry

end SandsSauerWoodrow
