-- Prove2me | Theorems.Thm_StrongPerfectGraph_EvenPrism_replaced_prism_triangle_neighbors
-- name    : StrongPerfectGraph.EvenPrism.replaced_prism_triangle_neighbors
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:27:40.230641+00:00
-- url     : https://prove2.me/theorems/14bf92a0-8e40-44dd-aa5a-f64ff8cd4b4f
-- title:
--   7.4 — replacing one even prism path preserves two neighbours
-- statement:
--   Let $P_1,P_2,P_3$ form a prism in a Berge graph, with each path of even length at least two and end triangles $A=\{a_1,a_2,a_3\}$ and $B=\{b_1,b_2,b_3\}$. Replace $P_1$ by a path $P'_1$ from $a'_1$ to $b_1$ so that $P'_1,P_2,P_3$ again form a prism. If a vertex $y$ has at least two neighbours in each of $A$ and $B$, then
--
--   $$|N_G(y)\cap\{a'_1,a_2,a_3\}|\ge2.$$
--
--   This controls a major vertex when a prism path changes.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), https://doi.org/10.4007/annals.2006.164.51, p. 93, 7.4

import Definitions.Def_StrongPerfectGraph_EvenPrism_Prism

namespace StrongPerfectGraph.EvenPrism

theorem replaced_prism_triangle_neighbors {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : StrongPerfectGraph.Main.IsBerge G)
    (a b a' : Fin 3 → V) (R R' : Fin 3 → List V)
    (hR : IsPrism G a b R)
    (heven : ∀ i, Even ((R i).length - 1) ∧ 2 ≤ (R i).length - 1)
    (hR' : IsPrism G a' b R')
    (hshared : ∀ i : Fin 3, i ≠ 0 → R' i = R i ∧ a' i = a i)
    (y : V)
    (hyA : ∃ i j, i ≠ j ∧ G.Adj y (a i) ∧ G.Adj y (a j))
    (hyB : ∃ i j, i ≠ j ∧ G.Adj y (b i) ∧ G.Adj y (b j)) :
    ∃ i j, i ≠ j ∧ G.Adj y (a' i) ∧ G.Adj y (a' j) := by sorry

end StrongPerfectGraph.EvenPrism
