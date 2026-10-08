-- Prove2me | Theorems.Thm_SpectralSparsify_Decomp_eq_12_cut_union
-- name    : SpectralSparsify.Decomp.eq_12_cut_union
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:34:21.002484+00:00
-- url     : https://prove2.me/theorems/b3ac4802-cf87-4f66-b080-c18f5051b5d3
-- title:
--   (12), first inequality — |E(R ∪ S, B − (R ∪ S))| ≤ |E(S, B − S)| + |E(R, B − S − R)|
-- statement:
--   Let $G=(V,E)$ be a finite simple graph, let $B\subseteq V$, let $S\subseteq B$ and let $R\subseteq B-S$. Put $T=R\cup S$. Then
--   $$|E(T,B-T)|=|E(R\cup S,\,B-(R\cup S))|\le|E(S,B-S)|+|E(R,\,B-S-R)|.$$
--
--   Every edge leaving $T$ inside $B$ either leaves $S$ into $B-S$ or leaves $R$ into the rest of $B-S$. In the proof of Lemma 7.2 this inequality, combined with the sparsity of $S$ and $R$, shows that the merged set $T$ is again sparse.
-- source:
--   D. A. Spielman, S.-H. Teng, Spectral Sparsification of Graphs, arXiv:0808.4134v3, p. 18, proof of Lemma 7.2, display (12), first inequality

import Mathlib
import Definitions.Def_SpectralSparsify_Decomp_cutEdges

namespace SpectralSparsify.Decomp

/-- (12), first inequality (arXiv:0808.4134v3, proof of Lemma 7.2, p. 18): for `S ⊆ B`,
`R ⊆ B - S` and `T = R ∪ S`,
`|E(R ∪ S, B - (R ∪ S))| ≤ |E(S, B - S)| + |E(R, B - S - R)|`. -/
theorem eq_12_cut_union {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (B S R : Finset V) (hSB : S ⊆ B) (hRB : R ⊆ B \ S) :
    cutEdges G (R ∪ S) (B \ (R ∪ S)) ≤ cutEdges G S (B \ S) + cutEdges G R ((B \ S) \ R) := by sorry

end SpectralSparsify.Decomp
