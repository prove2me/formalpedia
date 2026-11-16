-- Prove2me | Theorems.Thm_STCSublinear1377_Main_Supplement_lemma_2_3
-- name    : STCSublinear1377.Main.Supplement.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:23:57.831431+00:00
-- url     : https://prove2.me/theorems/5a882a9f-e6bf-44aa-9b9c-61b51a290600
-- title:
--   Lemma 2.3 — Internal spanning trees of connected induced subgraphs
-- statement:
--   Let $G$ be a connected simple unweighted graph on $n\ge2$ vertices with $k=\mathrm{STC}(G)$. Let $P\subseteq V(G)$ be nonempty with $G[P]$ connected and put $D_P=\max_{u\in P}d_G(u)$ (degrees in $G$). For every $r>0$ there are a randomized polynomial-time algorithm and a constant $C>0$, independent of $G$ and $P$, which on input $G$ and $P$ always outputs a spanning tree $T_P$ of $G[P]$, and with probability at least $1-n^{-r}$
--
--   $$c(G[P],T_P)\le C\,k\,\max\{D_P,\ b_G(P)\}\,\log^{3/2}n ,$$
--
--   where $b_G(P)$ is the number of edges of $G$ leaving $P$. The routine builds the internal trees of the sub-regions in steps (1) and (3a) of the simple algorithm.
--
--   Differences from the source:
--   - reading: Kolman's algorithm [Kol26] constructs a spanning tree T_P with c(G[P],T_P) = O(k max{D_P, b_G(P)} log^{3/2} n) → for each r > 0 a randomized polynomial-time machine and an absolute C: every tape outputs a spanning tree of G[P], and with probability ≥ 1 − n^{−r} the bound holds; reason: the cited algorithm is the randomized hereditary-bisection routine of Lemma 1.3, whose guarantee holds with high probability; O(·) is an absolute constant
--   - encoding: the graph G and the set P → the adjacency table of G followed by the indicator bits of P; reason: same instances
-- source:
--   Sunny Atalig, Marek Chrobak, Petr Kolman, Hans Raj Tiwary, Sublinear Approximations for Spanning Tree Congestion, STOC 2027 submission #1377 (October 2026), pinned submission, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1377.pdf, Lemma 2.3 and (2.2), PDF/printed p.4; proof p.5

import Definitions.Def_STCSublinear1377_Main_Supplement_Section2
set_option autoImplicit false

namespace STCSublinear1377.Main.Supplement

/-- Lemma 2.3: internal trees of connected induced subgraphs, with original degrees and global
boundary; every tape gives a spanning tree of `G[P]`. -/
theorem lemma_2_3 :
    ∀ r : ℝ, 0 < r → ∃ a : RandomDataMachine, ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 2 ≤ n → ∀ g : Table n, isInput g →
      ∀ P : Finset (Fin n), (original g).connectedSet P →
        let input := graphTapeBits g [] ++ setBits P
        (∀ tape : Fin (a.tapeLength input) → Bool,
          let out := a.output input tape
          out.length = n * n ∧ ((original g).induced P).tree (outputTable n out)) ∧
        dataProbability a input (fun out =>
          ((original g).induced P).congestion (outputTable n out) ≤
            C * (stc g : ℝ) * max (maxDegreeOn g P) ((original g).boundary P) *
              Real.rpow (Real.log (n : ℝ)) (3 / 2 : ℝ)) ≥
          1 - Real.rpow (n : ℝ) (-r) := by sorry

end STCSublinear1377.Main.Supplement
