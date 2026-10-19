-- Prove2me | Theorems.Thm_SandsSauerWoodrow_two_coloured_tournament_source
-- name    : SandsSauerWoodrow.two_coloured_tournament_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-17T01:04:30.649069+00:00
-- url     : https://prove2.me/theorems/579eac76-f218-4575-8f98-350b0c966a6c
-- title:
--   Sands-Sauer-Woodrow Corollary 2, source orientation: a two-coloured tournament has a monochromatic source
-- statement:
--   This is Corollary 2 of Sands, Sauer and Woodrow (J. Combin. Theory Ser. B **33** (1982), 271–275, p. 273) in the orientation used by the platform's definition `IsMonochromaticSource`, which is the orientation of the open problem the platform carries as `OPG1808.root_problem`.
--
--   Let $T$ be a tournament on a nonempty finite set $V$ of vertices — every two distinct vertices joined by exactly one arc — whose arcs carry only the colours $0$ and $1$. Then there is a vertex $s$ such that **every** vertex $t$ of $T$ is reachable from $s$ by a directed path all of whose arcs have one common colour, the colour being allowed to depend on $t$. Equivalently, in the vocabulary of the platform's module for this problem, $s$ is a **monochromatic source** of $T$.
--
--   Reversing every arc of a tournament gives a tournament, and reversing a monochromatic path gives a monochromatic path, so this statement and the one directing paths towards the distinguished vertex are equivalent; the source paper states the latter, and both are asked for here.
--
--   **Formalization Note.** The hypothesis restricts colours on arcs only. Nonemptiness of $V$ is required, as for the sink formulation.
-- source:
--   B. Sands, N. Sauer, R. Woodrow, On monochromatic paths in edge-coloured digraphs, J. Combin. Theory Ser. B 33 (1982), no. 3, 271-275. Theorem 1 (pp. 271-273); Corollary 2 (p. 273); Theorem 3 (pp. 274-275); PROBLEM (p. 275).

import Definitions.Def_opg1808_colored_tournaments

open OPG1808

universe u

namespace SandsSauerWoodrow

theorem two_coloured_tournament_source {V : Type u} [Fintype V] [Nonempty V]
    (D : Digraph V) (color : ArcColoring V) (htournament : IsTournament D)
    (htwo : ∀ u v, D u v → (color u v = 0 ∨ color u v = 1)) :
    ∃ s : V, IsMonochromaticSource D color s := by sorry

end SandsSauerWoodrow
