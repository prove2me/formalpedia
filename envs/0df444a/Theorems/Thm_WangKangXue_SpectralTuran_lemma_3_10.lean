-- Prove2me | Theorems.Thm_WangKangXue_SpectralTuran_lemma_3_10
-- name    : WangKangXue.SpectralTuran.lemma_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T14:29:41.149978+00:00
-- url     : https://prove2.me/theorems/f22855ba-b87b-4ab1-bc26-73f9a7714624
-- title:
--   Lemma 3.10 — the maximum partition is balanced: |n_i − n_j| ≤ 1
-- statement:
--   Let $r \ge 2$ and let $F$ be a graph whose extremal graphs are $T_{n,r}$ plus a fixed number $a$ of edges for all large $n$ (the standing hypothesis of Section 3). There is $N$ such that for every $n \ge N$, every $n$-vertex $F$-free graph $G$ of maximum spectral radius and every partition $V(G) = V_1 \cup \dots \cup V_r$ maximising $\sum_{i<j} e(V_i, V_j)$, the part sizes $n_i = |V_i|$ satisfy
--   $$
--   |n_i - n_j| \le 1 \qquad \text{for all } 1 \le i < j \le r .
--   $$
--
--   So the complete $r$-partite graph on the maximum partition is the Turán graph $T_{n,r}$, which lets the final step compare $G$ with an extremal graph on the same partition.
--
--   **Formalization Note** The sizes are compared in $\mathbb Z$ for all pairs $i, j$. The statement quantifies over every maximising partition (see Lemma 3.3).
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, p. 13, Lemma 3.10

import Mathlib
import Definitions.Def_WangKangXue_SpectralTuran_specRad
import Definitions.Def_WangKangXue_SpectralTuran_IsSpectralExtremal
import Definitions.Def_WangKangXue_SpectralTuran_TuranPlusEdges
import Definitions.Def_WangKangXue_SpectralTuran_IsMaxCut

namespace WangKangXue.SpectralTuran

open Classical

/-- **Lemma 3.10** (Wang–Kang–Xue, arXiv:2203.10831v1, p. 13). Under the standing hypotheses of
Section 3, for all large `n`: for every `n`-vertex `F`-free graph `G` of maximum spectral radius
and every partition `V_1 ∪ ⋯ ∪ V_r` maximising `∑_{i<j} e(V_i, V_j)`, the part sizes
`n_i = |V_i|` satisfy `|n_i − n_j| ≤ 1` for all `i, j`. -/
theorem lemma_3_10 {W : Type*} [Fintype W] (F : SimpleGraph W) (r a : ℕ) (hr : 2 ≤ r)
    (hF : TuranPlusEdges F r a) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), IsSpectralExtremal F G →
      ∀ P : Fin n → Fin r, IsMaxCut G P →
        ∀ i j : Fin r, |((part P i).card : ℤ) - ((part P j).card : ℤ)| ≤ 1 := by sorry

end WangKangXue.SpectralTuran
