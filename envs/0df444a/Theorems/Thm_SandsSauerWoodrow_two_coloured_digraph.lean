-- Prove2me | Theorems.Thm_SandsSauerWoodrow_two_coloured_digraph
-- name    : SandsSauerWoodrow.two_coloured_digraph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-17T01:04:22.027184+00:00
-- url     : https://prove2.me/theorems/efe51c36-8e3c-4da1-bbf9-87e0fd5bbd8f
-- title:
--   Sands-Sauer-Woodrow Theorem 1: two-coloured digraphs have a monochromatically independent set reached by all outsiders
-- statement:
--   This is Theorem 1 of Sands, Sauer and Woodrow, *On monochromatic paths in edge-coloured digraphs*, J. Combin. Theory Ser. B **33** (1982), 271–275, stated on p. 271 with its proof on pp. 271–273.
--
--   Let $G$ be a directed graph on an arbitrary set $V$ of vertices — possibly infinite, with loops and multiple edges allowed by the source — whose arcs are coloured with two colours, and suppose that $G$ has no **monochromatic infinite outward path**: no injective sequence $x_0, x_1, x_2, \dots$ of vertices all of whose consecutive arcs $x_n \to x_{n+1}$ carry one common colour. Then there is a set $S$ of vertices such that
--
--   1. $S$ is **monochromatically independent**: no two distinct members of $S$ are connected by a monochromatic directed path in either direction; and
--   2. every vertex $x \notin S$ reaches some member of $S$ by a monochromatic directed path.
--
--   No nonemptiness of $S$ is imposed: for a nonempty vertex set it follows, since a vertex outside an empty $S$ would have nothing to reach. The theorem is the general statement of which the two-coloured tournament corollary is a special case; over an infinite vertex set the source's proof uses Zorn's lemma.
--
--   **Formalization Note.** The two colours are the values $0$ and $1$; the hypothesis constrains colours on arcs, which is all the conclusion uses. The source's paths have pairwise distinct vertices, which is what the injectivity of the sequence above records; the source's own definition of independence is the one in the first clause.
-- source:
--   B. Sands, N. Sauer, R. Woodrow, On monochromatic paths in edge-coloured digraphs, J. Combin. Theory Ser. B 33 (1982), no. 3, 271-275. Theorem 1 (pp. 271-273); Corollary 2 (p. 273); Theorem 3 (pp. 274-275); PROBLEM (p. 275).

import Definitions.Def_opg1808_colored_tournaments
import Definitions.Def_SandsSauerWoodrow_MonoIndependent

open OPG1808

universe u

namespace SandsSauerWoodrow

theorem two_coloured_digraph {V : Type u} (D : Digraph V) (color : ArcColoring V)
    (htwo : ∀ u v, D u v → (color u v = 0 ∨ color u v = 1))
    (hno : NoMonoInfiniteOutwardPath D color) :
    ∃ S : Set V, MonoIndependent D color S ∧
      ∀ x : V, x ∉ S → ∃ s ∈ S, MonochromaticallyReaches D color x s := by sorry

end SandsSauerWoodrow
