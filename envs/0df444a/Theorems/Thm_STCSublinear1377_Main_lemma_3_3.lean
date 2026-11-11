-- Prove2me | Theorems.Thm_STCSublinear1377_Main_lemma_3_3
-- name    : STCSublinear1377.Main.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:39:58.594938+00:00
-- url     : https://prove2.me/theorems/01933ac3-e054-4151-a973-ba72320385d2
-- title:
--   Lemma 3.3 — Both loads under simultaneous bag expansion
-- statement:
--   Let $Q$ be a connected positive-weight graph's quotient with a spanning tree $T$. Refine any disjoint collection of its bags into connected partitions, choose internal spanning trees $T_A$, and substitute them using the selected original endpoints of the old tree edges. The resulting $T'$ spans the refined quotient $Q'$. For each expanded bag $A$ represented by $a$, every new tree edge $e$ inside it and every refined vertex $b$ inside it satisfy
--
--   $$c_{Q',T'}(e)\le c_{J_A,T_A}(e)+\ell_{Q,T}(a),\qquad
--   \ell_{Q',T'}(b)\le\ell_{J_A,T_A}(b)+\ell_{Q,T}(a).$$
--
--   Every surviving old tree edge and every unexpanded old vertex retain their loads exactly. This statement covers a single expansion and simultaneous disjoint expansions, with arbitrary positive real edge weights. It provides both quantities required for recursive tree substitution.
--
--   Differences from the source:
--   - encoding: single and simultaneous expansions described by bag substitutions → one Expansion record with a chosen set of refined bags and an explicit result adjacency table; reason: a singleton set of refined bags is the single-bag statement, while the same record expresses the source simultaneous extension
--   - encoding: arbitrary positive-weight finite graphs → real weight matrices and finite named bag maps; reason: each undirected demand is counted once and selected original endpoints are retained without changing any source instance
-- source:
--   Sunny Atalig, Marek Chrobak, Petr Kolman, Hans Raj Tiwary, Sublinear Approximations for Spanning Tree Congestion, STOC 2027 submission #1377 (October 2026), pinned submission, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1377.pdf, Lemma 3.3, (3.2)–(3.3), PDF/printed p.9; proof p.10

import Definitions.Def_STCSublinear1377_Main_Expansion
set_option autoImplicit false

namespace STCSublinear1377.Main

/-- Arbitrary positive real weights and simultaneous expansions, including the single-bag
case, both kinds of load, and equality of surviving old loads. -/
theorem lemma_3_3 :
    ∀ n : ℕ, ∀ f : WeightedGraph n, f.positive → f.connected → ∀ x : Expansion f,
      x.fine.quotient.tree x.result ∧
      (∀ a ∈ x.refined, ∀ b ∈ x.fine.names, ∀ c ∈ x.fine.names,
        x.parent b = a → x.parent c = a → x.localTree a b c = true →
          x.fine.quotient.edgeLoad x.result b c ≤
            (x.localGraph a).edgeLoad (x.localTree a) b c +
              x.coarse.quotient.vertexLoad x.oldTree a) ∧
      (∀ a ∈ x.refined, ∀ b ∈ x.fine.names, x.parent b = a →
        x.fine.quotient.vertexLoad x.result b ≤
          (x.localGraph a).vertexLoad (x.localTree a) b +
            x.coarse.quotient.vertexLoad x.oldTree a) ∧
      (∀ b ∈ x.fine.names, ∀ c ∈ x.fine.names,
        x.parent b ≠ x.parent c → x.result b c = true →
          x.fine.quotient.edgeLoad x.result b c =
            x.coarse.quotient.edgeLoad x.oldTree (x.parent b) (x.parent c)) ∧
      (∀ a ∈ x.coarse.names, a ∉ x.refined →
        x.fine.quotient.vertexLoad x.result a =
          x.coarse.quotient.vertexLoad x.oldTree a) := by sorry

end STCSublinear1377.Main
