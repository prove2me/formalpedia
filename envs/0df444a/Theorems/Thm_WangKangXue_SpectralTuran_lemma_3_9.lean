-- Prove2me | Theorems.Thm_WangKangXue_SpectralTuran_lemma_3_9
-- name    : WangKangXue.SpectralTuran.lemma_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T14:28:36.305566+00:00
-- url     : https://prove2.me/theorems/b27e2cb9-8ffa-4d73-a6f9-dffcdb945a6b
-- title:
--   Lemma 3.9 — e(G_in) − e(G_out) ≤ a
-- statement:
--   Let $r \ge 2$ and let $F$ be a graph whose extremal graphs are $T_{n,r}$ plus a fixed number $a$ of edges for all large $n$ (the standing hypothesis of Section 3). There is $N$ such that for every $n \ge N$, every $n$-vertex $F$-free graph $G$ of maximum spectral radius and every partition $V(G) = V_1 \cup \dots \cup V_r$ maximising $\sum_{i<j} e(V_i, V_j)$, the following holds. Let $G_{in} = \bigcup_{i=1}^r G[V_i]$, let $K = K_r(n_1,\dots,n_r)$ be the complete $r$-partite graph on $V_1,\dots,V_r$ ($n_i = |V_i|$), and let $G_{out}$ be the graph on $V(G)$ with edge set $E(K) \setminus E(G)$. Then
--   $$
--   e(G_{in}) - e(G_{out}) \le a .
--   $$
--
--   Since $e(G) = e(G_{in}) + e(K) - e(G_{out})$, the lemma compares $G$ with the complete $r$-partite graph on its own partition.
--
--   **Formalization Note** $e(G_{in})$ is written as $\sum_i e(G[V_i])$ (the parts are disjoint), and $G_{out}$ as the graph difference $K \setminus G$; the difference is taken in $\mathbb Z$. The statement quantifies over every maximising partition (see Lemma 3.3).
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, p. 12, Lemma 3.9 (G_in, K, G_out defined just before it)

import Mathlib
import Definitions.Def_WangKangXue_SpectralTuran_specRad
import Definitions.Def_WangKangXue_SpectralTuran_IsSpectralExtremal
import Definitions.Def_WangKangXue_SpectralTuran_TuranPlusEdges
import Definitions.Def_WangKangXue_SpectralTuran_edgesIn
import Definitions.Def_WangKangXue_SpectralTuran_IsMaxCut

namespace WangKangXue.SpectralTuran

open Classical

/-- **Lemma 3.9** (Wang–Kang–Xue, arXiv:2203.10831v1, p. 12). Under the standing hypotheses of
Section 3, for all large `n`: for every `n`-vertex `F`-free graph `G` of maximum spectral radius
and every partition `V_1 ∪ ⋯ ∪ V_r` maximising `∑_{i<j} e(V_i, V_j)`,
`e(G_in) − e(G_out) ≤ a`, where `G_in = ⋃_i G[V_i]` (so `e(G_in) = ∑_i e(G[V_i])`) and `G_out`
has the edges of `K = K_r(n_1, …, n_r)` (on the parts `V_i`) that are not edges of `G`. -/
theorem lemma_3_9 {W : Type*} [Fintype W] (F : SimpleGraph W) (r a : ℕ) (hr : 2 ≤ r)
    (hF : TuranPlusEdges F r a) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), IsSpectralExtremal F G →
      ∀ P : Fin n → Fin r, IsMaxCut G P →
        ((∑ i, edgesIn G (part P i) : ℕ) : ℤ) - ((completePartite P \ G).edgeFinset.card : ℤ)
          ≤ a := by sorry

end WangKangXue.SpectralTuran
