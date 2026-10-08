-- Prove2me | Theorems.Thm_WangKangXue_SpectralTuran_lemma_2_3
-- name    : WangKangXue.SpectralTuran.lemma_2_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T14:22:57.073981+00:00
-- url     : https://prove2.me/theorems/9a5da411-424d-41c9-9efe-93377bd6ddb7
-- title:
--   Lemma 2.3 — a proper subgraph of a connected graph has smaller λ
-- statement:
--   Let $G$ be a connected finite simple graph and let $G'$ be a proper spanning subgraph of $G$, i.e. $V(G') = V(G)$, $E(G') \subseteq E(G)$ and $E(G') \ne E(G)$. Then
--   $$
--   \lambda(G') < \lambda(G),
--   $$
--   where $\lambda$ denotes the largest adjacency eigenvalue.
--
--   This strict monotonicity, a consequence of the Perron–Frobenius theorem for irreducible nonnegative matrices, is the tool that turns "adding an edge keeps the graph $F$-free" into a contradiction with spectral maximality (Lemma 3.1 and the proofs of Lemmas 3.6–3.8).
--
--   **Formalization Note** The paper's "proper subgraph" also allows $G'$ to have fewer vertices. That case follows from the spanning case, because adding isolated vertices to $G'$ does not change $\lambda(G')$; the statement here is the spanning case.
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, p. 3, Lemma 2.3

import Mathlib
import Definitions.Def_WangKangXue_SpectralTuran_specRad

namespace WangKangXue.SpectralTuran

open Classical

/-- **Lemma 2.3** (Wang–Kang–Xue, arXiv:2203.10831v1, p. 3). If `G` is connected and `G'` is a
proper (spanning) subgraph of `G`, then `λ(G') < λ(G)`. -/
theorem lemma_2_3 {V : Type*} [Fintype V] [DecidableEq V] (G G' : SimpleGraph V)
    (hG : G.Connected) (hle : G' ≤ G) (hne : G' ≠ G) :
    specRad G' < specRad G := by sorry

end WangKangXue.SpectralTuran
