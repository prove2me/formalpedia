-- Prove2me | Theorems.Thm_WangKangXue_SpectralTuran_lemma_3_3
-- name    : WangKangXue.SpectralTuran.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T14:25:31.869986+00:00
-- url     : https://prove2.me/theorems/e4e81fe4-726d-41ae-8a79-fb8fa7f0cfcc
-- title:
--   Lemma 3.3 — e(G) ≥ e(T_{n,r}) − εn², and a maximum partition is nearly balanced and nearly independent
-- statement:
--   Let $r \ge 2$ and let $F$ be a graph whose extremal graphs are $T_{n,r}$ plus a fixed number $a$ of edges for all large $n$ (the standing hypothesis of Section 3). For every $\varepsilon > 0$ there is $n_0$ such that for every $n \ge n_0$ and every $n$-vertex $F$-free graph $G$ of maximum spectral radius:
--
--   1. $e(G) \ge e(T_{n,r}) - \varepsilon n^2$;
--   2. for every partition $V(G) = V_1 \cup \dots \cup V_r$ for which $\sum_{1 \le i < j \le r} e(V_i, V_j)$ attains the maximum,
--   $$
--   \sum_{i=1}^r e(V_i) \le \varepsilon n^2 \qquad\text{and}\qquad \Big(\frac1r - 3\sqrt{\varepsilon}\Big)n < |V_i| < \Big(\frac1r + 3\sqrt{\varepsilon}\Big)n \quad (i \in [r]).
--   $$
--
--   Here $e(V_i)$ is the number of edges of $G$ inside $V_i$. This is the first structural description of the extremal graph: it is close to $T_{n,r}$ with respect to every maximum $r$-cut.
--
--   **Formalization Note** The paper states that $G$ *has* such a partition; its proof shows that *every* maximising partition has these properties, and the later lemmas use nothing else about the partition, so the statement quantifies over all maximising partitions (a stronger form). Partitions are labellings $P : \mathrm{Fin}\ n \to \mathrm{Fin}\ r$.
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, pp. 4–5, Lemma 3.3

import Mathlib
import Definitions.Def_WangKangXue_SpectralTuran_specRad
import Definitions.Def_WangKangXue_SpectralTuran_IsSpectralExtremal
import Definitions.Def_WangKangXue_SpectralTuran_TuranPlusEdges
import Definitions.Def_WangKangXue_SpectralTuran_edgesIn
import Definitions.Def_WangKangXue_SpectralTuran_IsMaxCut

namespace WangKangXue.SpectralTuran

open Classical

/-- **Lemma 3.3** (Wang–Kang–Xue, arXiv:2203.10831v1, pp. 4–5). Under the standing hypotheses of
Section 3: for every `ε > 0` there is `n₀` such that for `n ≥ n₀`, every `n`-vertex `F`-free graph
`G` of maximum spectral radius has `e(G) ≥ e(T_{n,r}) − ε n²`, and every partition
`V(G) = V_1 ∪ ⋯ ∪ V_r` maximising `∑_{i<j} e(V_i, V_j)` satisfies `∑_i e(V_i) ≤ ε n²` and
`(1/r − 3√ε) n < |V_i| < (1/r + 3√ε) n` for each `i`. -/
theorem lemma_3_3 {W : Type*} [Fintype W] (F : SimpleGraph W) (r a : ℕ) (hr : 2 ≤ r)
    (hF : TuranPlusEdges F r a) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G : SimpleGraph (Fin n), IsSpectralExtremal F G →
      ((SimpleGraph.turanGraph n r).edgeFinset.card - ε * (n : ℝ) ^ 2 ≤ G.edgeFinset.card) ∧
      ∀ P : Fin n → Fin r, IsMaxCut G P →
        ((∑ i, edgesIn G (part P i) : ℕ) : ℝ) ≤ ε * (n : ℝ) ^ 2 ∧
        ∀ i : Fin r,
          (1 / (r : ℝ) - 3 * Real.sqrt ε) * n < (part P i).card ∧
          ((part P i).card : ℝ) < (1 / (r : ℝ) + 3 * Real.sqrt ε) * n := by sorry

end WangKangXue.SpectralTuran
