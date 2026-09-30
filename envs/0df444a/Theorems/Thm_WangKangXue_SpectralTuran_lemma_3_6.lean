-- Prove2me | Theorems.Thm_WangKangXue_SpectralTuran_lemma_3_6
-- name    : WangKangXue.SpectralTuran.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T14:26:34.787883+00:00
-- url     : https://prove2.me/theorems/d8166861-422a-4c39-bc03-9c8e65df0730
-- title:
--   Lemma 3.6 — L is empty and e(G[V_i]) ≤ a
-- statement:
--   Let $r \ge 2$ and let $F$ be a graph whose extremal graphs are $T_{n,r}$ plus a fixed number $a$ of edges for all large $n$ (the standing hypothesis of Section 3). There is $\varepsilon_0 > 0$ such that for every $0 < \varepsilon < \varepsilon_0$ there is $n_0$ with the following property. For every $n \ge n_0$, every $n$-vertex $F$-free graph $G$ of maximum spectral radius, and every partition $V(G) = V_1 \cup \dots \cup V_r$ maximising $\sum_{i<j} e(V_i, V_j)$:
--
--   1. the set
--   $$
--   L = \Big\{ v \in V(G) : d(v) \le \Big(1 - \frac1r - 3r\varepsilon^{1/3}\Big)n \Big\}
--   $$
--   of (6) is empty, i.e. every vertex has degree greater than $(1 - 1/r - 3r\varepsilon^{1/3})n$;
--   2. $e(G[V_i]) \le a$ for each $i \in [r]$.
--
--   So every part of a maximum partition spans at most $a$ edges and no vertex has small degree.
--
--   **Formalization Note** The paper fixes "sufficiently small" constants $\theta, \varepsilon$ (Lemma 3.4); this is rendered as the threshold $\varepsilon_0$. $\varepsilon^{1/3}$ is the real cube root (`Real.rpow`). The statement quantifies over every maximising partition (see Lemma 3.3).
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, p. 9, Lemma 3.6 (with L from Eq. (6), p. 5)

import Mathlib
import Definitions.Def_WangKangXue_SpectralTuran_specRad
import Definitions.Def_WangKangXue_SpectralTuran_IsSpectralExtremal
import Definitions.Def_WangKangXue_SpectralTuran_TuranPlusEdges
import Definitions.Def_WangKangXue_SpectralTuran_edgesIn
import Definitions.Def_WangKangXue_SpectralTuran_IsMaxCut

namespace WangKangXue.SpectralTuran

open Classical

/-- **Lemma 3.6** (Wang–Kang–Xue, arXiv:2203.10831v1, p. 9). Under the standing hypotheses of
Section 3, for every sufficiently small `ε > 0` and all large `n`: for every `n`-vertex `F`-free
graph `G` of maximum spectral radius and every partition `V_1 ∪ ⋯ ∪ V_r` maximising
`∑_{i<j} e(V_i, V_j)`, the set `L = {v : d(v) ≤ (1 − 1/r − 3 r ε^{1/3}) n}` of (6) is empty and
`e(G[V_i]) ≤ a` for each `i`. -/
theorem lemma_3_6 {W : Type*} [Fintype W] (F : SimpleGraph W) (r a : ℕ) (hr : 2 ≤ r)
    (hF : TuranPlusEdges F r a) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G : SimpleGraph (Fin n), IsSpectralExtremal F G →
        ∀ P : Fin n → Fin r, IsMaxCut G P →
          (∀ v : Fin n,
            (1 - 1 / (r : ℝ) - 3 * r * ε ^ ((1 : ℝ) / 3)) * n < (G.degree v : ℝ)) ∧
          ∀ i : Fin r, edgesIn G (part P i) ≤ a := by sorry

end WangKangXue.SpectralTuran
