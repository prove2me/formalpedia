-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P02_lemma_5_4
-- name    : QAlgorithms.Papers.Independent.Claimed50.P02.lemma_5_4
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T08:30:18.853885+00:00
-- url     : https://prove2.me/theorems/53d64678-7dc8-4c87-9c27-f480b542cf86
-- title:
--   Lemma 5.4: content vectors distinguish physical paths
-- statement:
--   Let $d\ge2$, $p,q\ge0$, and let $S,T$ be root-to-level-$(p+q)$ paths in the physical Bratteli graph. Before the wall a step adds one left cell; after the wall it removes one left cell or adds one right cell. At every vertex $(\lambda^l,\lambda^r)$ require $\operatorname{len}(\lambda^l)+\operatorname{len}(\lambda^r)\le d$. Give a left addition at $(i,j)$ content $j-i$, a left removal content $i-j$, and a right addition content $j-i+d$. If $c_T$ is the complete vector of edge contents, then
--   $$
--   S=T\quad\Longleftrightarrow\quad c_S=c_T.
--   $$
--   Thus the full content vector labels a physical path uniquely, including the unique empty path when $p=q=0$.
-- source:
--   Linear programming with unitary-equivariant constraints, arXiv:2207.05713v2, PDF p. 28, Lemma 5.4: content vectors distinguish physical paths

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P02

namespace QAlgorithms.Papers.Independent.Claimed50.P02

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P69 (Sites choi)

noncomputable section

/-- Paper p.28, Lemma 5.4: content vectors distinguish paths in the physical,
d-truncated graph, including the empty path when p=q=0. -/
theorem lemma_5_4 {d p q : ℕ} (hd : 2 ≤ d) (S T : PhysicalPath d p q) :
    S = T ↔ pathContent S = pathContent T := by sorry

end

end QAlgorithms.Papers.Independent.Claimed50.P02
