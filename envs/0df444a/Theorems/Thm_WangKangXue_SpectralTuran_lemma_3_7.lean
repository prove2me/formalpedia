-- Prove2me | Theorems.Thm_WangKangXue_SpectralTuran_lemma_3_7
-- name    : WangKangXue.SpectralTuran.lemma_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T14:27:22.745512+00:00
-- url     : https://prove2.me/theorems/077e9dc3-0bc7-4666-97e3-32e15324c800
-- title:
--   Lemma 3.7 — at most 2a vertices of V_i have a neighbour in V_i; the others see all of V ∖ V_i
-- statement:
--   Let $r \ge 2$ and let $F$ be a graph whose extremal graphs are $T_{n,r}$ plus a fixed number $a$ of edges for all large $n$ (the standing hypothesis of Section 3). There is $N$ such that for every $n \ge N$, every $n$-vertex $F$-free graph $G$ of maximum spectral radius, every partition $V(G) = V_1 \cup \dots \cup V_r$ maximising $\sum_{i<j} e(V_i, V_j)$ and every $i \in [r]$, put
--   $$
--   B_i = \{u \in V_i : d_{V_i}(u) \ge 1\}, \qquad C_i = V_i \setminus B_i ,
--   $$
--   where $d_{V_i}(u)$ is the number of neighbours of $u$ in $V_i$. Then
--
--   1. $|B_i| \le 2a$;
--   2. every vertex $u \in C_i$ is adjacent to all vertices of $V \setminus V_i$.
--
--   Thus $G$ contains the complete $r$-partite graph on $C_1, \dots, C_r$ and differs from $K_r(|V_1|,\dots,|V_r|)$ only around the $O(1)$ vertices of $B_1 \cup \dots \cup B_r$.
--
--   **Formalization Note** The statement quantifies over every maximising partition (see Lemma 3.3).
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, p. 10, Lemma 3.7

import Mathlib
import Definitions.Def_WangKangXue_SpectralTuran_specRad
import Definitions.Def_WangKangXue_SpectralTuran_IsSpectralExtremal
import Definitions.Def_WangKangXue_SpectralTuran_TuranPlusEdges
import Definitions.Def_WangKangXue_SpectralTuran_IsMaxCut

namespace WangKangXue.SpectralTuran

open Classical

/-- **Lemma 3.7** (Wang–Kang–Xue, arXiv:2203.10831v1, p. 10). Under the standing hypotheses of
Section 3, for all large `n`: for every `n`-vertex `F`-free graph `G` of maximum spectral radius,
every partition `V_1 ∪ ⋯ ∪ V_r` maximising `∑_{i<j} e(V_i, V_j)` and every `i`, the set
`B_i = {u ∈ V_i : d_{V_i}(u) ≥ 1}` has `|B_i| ≤ 2a`, and every vertex `u` of `C_i = V_i \ B_i` is
adjacent to all vertices outside `V_i`. -/
theorem lemma_3_7 {W : Type*} [Fintype W] (F : SimpleGraph W) (r a : ℕ) (hr : 2 ≤ r)
    (hF : TuranPlusEdges F r a) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), IsSpectralExtremal F G →
      ∀ P : Fin n → Fin r, IsMaxCut G P → ∀ i : Fin r,
        ((part P i).filter (fun u => 1 ≤ ((G.neighborFinset u) ∩ part P i).card)).card
            ≤ 2 * a ∧
        ∀ u ∈ (part P i).filter (fun u => ((G.neighborFinset u) ∩ part P i).card = 0),
          ∀ w : Fin n, P w ≠ i → G.Adj u w := by sorry

end WangKangXue.SpectralTuran
