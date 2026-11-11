-- Prove2me | Theorems.Thm_RamseyLST_Main_theorem_47
-- name    : RamseyLST.Main.theorem_47
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:08:14.22618+00:00
-- url     : https://prove2.me/theorems/bf6c5b42-ecba-41d6-beaa-b22565bbe1a8
-- title:
--   Theorem 47 — every connected weighted graph has a strong $(\alpha, 1-O(\log\alpha/\alpha))$-Ramsey spanning tree inside any candidate core
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $G=(V,E,\ell)$ be a finite connected graph with positive edge lengths and shortest-path metric $d_G$, let $A\subseteq V$ be non-empty (a candidate core), and let $\alpha>5$ be real. Then there are a spanning tree $T$ of $G$, with the edge lengths of $G$ and shortest-path metric $d_T$, and a core $Z\subseteq A$ such that
--
--   $$|Z|\ \ge\ |A|^{\max\left(0,\ 1-C\frac{\log\alpha}{\alpha}\right)}\qquad\text{and}\qquad d_T(z,v)\le\alpha\,d_G(z,v)\quad\text{for every }z\in Z\text{ and every }v\in V,$$
--
--   where $\log$ is base 2. In the paper's words, $G$ has a strong $(\alpha,1-O(\log\alpha/\alpha))$-Ramsey spanning tree with candidate core $A$.
--
--   The case $A=V$ is the paper's main result, Theorem 1. It improves the previous exponent $1-O(\log\log n/\alpha)$ of Abraham et al., which is meaningful only for $\alpha=\Omega(\log\log n)$, to an exponent independent of $n$, tight up to the $\log\alpha$ factor. Applied iteratively, it yields Ramsey spanning tree covers of size $kn^{1/k}$ with distortion $O(k\log k)$ (Corollary 2).
--
--   Differences from the source:
--   - encoding: 1 − O(log α/α) → max(0, 1 − C log₂ α/α) for one absolute C > 0 chosen before G, A and α; reason: explicit constant for O(·); p. 10: an exponent stated without a lower bound is read as its maximum with 0
--   - encoding: a connected weighted graph G = (V, E, ℓ) and a spanning tree T → a finite type V with an ARTreeCover.WGraph, G.graph.Connected stated explicitly; T ≤ G.graph with T.IsTree, carrying G's lengths; distances in [0, ∞] and the stretch compared as d_T ≤ ofReal(α) · d_G; reason: the reused definition bundles neither finiteness nor connectivity; distances are finite on a connected graph
--   - encoding: Ramsey embedding: non-contractive (Definition 2) → not stated; reason: every spanning tree satisfies d_G ≤ d_T, since T is a subgraph of G; the identity embedding is injective
-- source:
--   Bartal, Hovav, Nearly Tight Low-Stretch Ramsey Spanning Trees, STOC 2027 submission (manuscript sha256 bcaed0afb9db0cccb453599c9f6915e958922563d3989766c4affc99a15de44d), p. 59 (PDF 63), Theorem 47 (Theorem 1, p. 2 (PDF 6), is the case A = V)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_RamseyLST_Main_RamseySpanningTree

open ARTreeCover

namespace RamseyLST.Main

/-- Theorem 47 (p. 59): there is an absolute constant `C > 0` such that every finite connected
weighted graph `G`, every non-empty candidate core `A ⊆ V` and every real `α > 5` admit a strong
`(α, max(0, 1 − C log₂ α / α))`-Ramsey spanning tree with candidate core `A`. -/
theorem theorem_47 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : WGraph V), G.graph.Connected →
        ∀ A : Finset V, A.Nonempty → ∀ α : ℝ, 5 < α →
          ∃ (T : SpanningTree G) (Z : Finset V),
            IsRamseySpanningTree true G T A Z α (max 0 (1 - C * Real.logb 2 α / α)) := by sorry

end RamseyLST.Main
