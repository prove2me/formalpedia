-- Prove2me | Theorems.Thm_StrongPerfectGraph_EvenPrism_anticonnected_prism_triangles
-- name    : StrongPerfectGraph.EvenPrism.anticonnected_prism_triangles
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:42:47.174208+00:00
-- url     : https://prove2.me/theorems/df6963ae-4a81-41e0-9963-32f2b375163b
-- title:
--   7.3 — an anticonnected set complete to prism triangles
-- statement:
--   Let $G$ be Berge and $Y$ an anticonnected vertex set disjoint from a prism with paths $P_1,P_2,P_3$, each of length greater than one. Suppose every vertex of $Y$ has at least two neighbours in each end triangle $A=\{a_1,a_2,a_3\}$ and $B=\{b_1,b_2,b_3\}$. Then
--
--   $$|\{a\in A:a\text{ is }Y\text{-complete}\}|\ge2,\qquad |\{b\in B:b\text{ is }Y\text{-complete}\}|\ge2.$$
--
--   The conclusion locates common neighbours of an anticonnected set at both ends of a prism.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), https://doi.org/10.4007/annals.2006.164.51, p. 93, 7.3

import Definitions.Def_StrongPerfectGraph_EvenPrism_Prism

namespace StrongPerfectGraph.EvenPrism

theorem anticonnected_prism_triangles {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : StrongPerfectGraph.Main.IsBerge G) (Y : Set V)
    (hY : StrongPerfectGraph.Main.IsConnectedSet Gᶜ Y) (a b : Fin 3 → V)
    (R : Fin 3 → List V) (hR : IsPrism G a b R)
    (hdisj : Disjoint Y (PrismVertices R))
    (hlong : ∀ i, 1 < (R i).length - 1)
    (hsat : ∀ y ∈ Y, IsMajor G a b y) :
    SaturatesPrism a b {v | CompleteTo G v Y} := by sorry

end StrongPerfectGraph.EvenPrism
