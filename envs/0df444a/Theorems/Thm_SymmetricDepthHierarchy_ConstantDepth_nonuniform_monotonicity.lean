-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_nonuniform_monotonicity
-- name    : SymmetricDepthHierarchy.ConstantDepth.nonuniform_monotonicity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:32:38.0013+00:00
-- url     : https://prove2.me/theorems/f8c71968-3348-46c0-9c56-1f5ba6eb87f4
-- title:
--   Theorem 3.7: $\mathrm{hom}_{F,N}\notin H_N(\mathcal F)$ when $F$ has a minor $G\notin\mathcal F$ and $N\ge\gamma(G)$
-- statement:
--   Let $\mathcal F$ be a class of simple graphs that contains the one-vertex graph $K_1$, is minor-closed, and is closed under weak oddomorphisms. Let $G\notin\mathcal F$ be a connected graph, let $F$ be a bipartite multigraph containing $G$ as a minor, and let
--   $$N\ge\gamma(G)=\sum_{v\in V(G)}2^{\deg_G(v)-1}.$$
--   Then $\mathrm{hom}_{F,N}\notin H_N(\mathcal F)$, the $K$-linear span of the homomorphism polynomials of all bipartite multigraphs whose underlying simple graph lies in $\mathcal F$ ($K$ of characteristic zero).
--
--   This is the general lower-bound tool, with a bound on $N$ that is single-exponential in the degrees of the minor $G$ only.
--
--   Differences from the source:
--   - encoding: a class of simple graphs → a set of FinGraph (finite vertex type in Type with a simple graph); reason: classes here are minor-closed or defined by an isomorphism-invariant predicate, so membership does not depend on the encoding
--   - encoding: γ(G) = ∑_v 2^{deg_G(v) − 1} → ∑_v 2^(deg_G(v) - 1) with natural-number subtraction; reason: every vertex of G has positive degree here (G connected with at least two vertices), so no truncation occurs
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 11 (PDF p. 14), Theorem 3.7; proof in §B.4, pp. 36–40 (PDF pp. 39–43)

import Mathlib
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Pattern
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Oddomorphism
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_CFI

open scoped Classical

namespace SymmetricDepthHierarchy.ConstantDepth

/-- Theorem 3.7, printed p. 11 (PDF p. 14). Let `𝓕` be a class of simple graphs that contains the
one-vertex graph `K₁`, is minor-closed, and is closed under weak oddomorphism. Let `G ∉ 𝓕` be a
connected graph, let `F` be a bipartite multigraph containing `G` as a minor, and let
`N ≥ γ(G) = ∑_{v ∈ V(G)} 2^{deg_G(v) − 1}`. Then `hom_{F,N} ∉ H_N(𝓕)`. -/
theorem nonuniform_monotonicity {K : Type} [Field K] [CharZero K] (𝓕 : GraphClass)
    (hK1 : K1 ∈ 𝓕) (hminor : MinorClosed 𝓕) (hodd : WeakOddClosed 𝓕) (G : FinGraph)
    (hG𝓕 : G ∉ 𝓕) (hG : G.G.Connected) (F : Pattern) (hFG : HadwigerConj.IsMinor G.G F.graph)
    (N : ℕ) (hN : cfiSize G.G ≤ N) : F.homPoly K N ∉ homSpan K N 𝓕 := by sorry

end SymmetricDepthHierarchy.ConstantDepth
