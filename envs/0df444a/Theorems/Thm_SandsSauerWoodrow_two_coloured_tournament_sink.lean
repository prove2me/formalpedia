-- Prove2me | Theorems.Thm_SandsSauerWoodrow_two_coloured_tournament_sink
-- name    : SandsSauerWoodrow.two_coloured_tournament_sink
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-17T01:04:10.580687+00:00
-- url     : https://prove2.me/theorems/5dea3d35-e4c8-480a-a28d-bc314df909a6
-- title:
--   Sands-Sauer-Woodrow Corollary 2: a two-coloured tournament has a monochromatic sink
-- statement:
--   This is Corollary 2 of Sands, Sauer and Woodrow, *On monochromatic paths in edge-coloured digraphs*, J. Combin. Theory Ser. B **33** (1982), 271–275, stated on p. 273.
--
--   Let $T$ be a tournament on a nonempty finite set $V$ of vertices — that is, a directed graph in which every two distinct vertices are joined by exactly one arc — and let each arc of $T$ carry one of three colours, only the colours $0$ and $1$ being used. Then there is a vertex $v$ such that for every vertex $x \neq v$ there is a directed path from $x$ to $v$ all of whose arcs have the same colour.
--
--   The common colour may depend on $x$, and the path is not required to be short: the source observes that no bound on its length is possible. In the source's terms the conclusion says that the tournament contains a **monochromatic sink**. This is the settled two-colour case of the question raised by Erdős on p. 275 of the same paper, whether three colours force either a rainbow directed triangle or such a vertex; that three-colour question is open.
--
--   **Formalization Note.** A colouring is a function on all ordered pairs of vertices; the hypothesis constrains its values only on arcs, which is all the conclusion depends on. The source allows loops and multiple edges; here a digraph is a relation and $T$ is a tournament, so neither occurs. Nonemptiness of $V$ is required: for an empty vertex set there is no vertex $v$ to exhibit.
-- source:
--   B. Sands, N. Sauer, R. Woodrow, On monochromatic paths in edge-coloured digraphs, J. Combin. Theory Ser. B 33 (1982), no. 3, 271-275. Theorem 1 (pp. 271-273); Corollary 2 (p. 273); Theorem 3 (pp. 274-275); PROBLEM (p. 275).

import Definitions.Def_opg1808_colored_tournaments

open OPG1808

universe u

namespace SandsSauerWoodrow

theorem two_coloured_tournament_sink {V : Type u} [Fintype V] [Nonempty V]
    (D : Digraph V) (color : ArcColoring V) (htournament : IsTournament D)
    (htwo : ∀ u v, D u v → (color u v = 0 ∨ color u v = 1)) :
    ∃ v : V, ∀ x : V, x ≠ v → MonochromaticallyReaches D color x v := by sorry

end SandsSauerWoodrow
