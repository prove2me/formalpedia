-- Prove2me | Theorems.Thm_TZLevelsADO_lemma_4
-- name    : TZLevelsADO.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:51:31.813177+00:00
-- url     : https://prove2.me/theorems/1dff3a42-ad43-4d9f-9c16-dd8760af1faa
-- title:
--   Lemma 4 (Section 3.5 in [TZ05]) — bunches have size $O(n^{1/k}\log n)$ w.h.p.
-- statement:
--   Let $G$ be a connected graph on $n$ vertices with positive real edge weights, let $k \ge 1$, fix a vertex $v_0$, and let $A_0 \supseteq \cdots \supseteq A_k$ be the randomly sampled hierarchy: each $A_{i+1}$ keeps each vertex of $A_i$ independently with probability $n^{-1/k}$, and $v_0$ is added to $A_1, \dots, A_{k-1}$. Let $B(u)$ be the bunch of $u$ in this hierarchy.
--
--   For every $c \in \mathbb N$ there is a constant $C$ (depending only on $c$) such that for all such $G$, $k$ and $v_0$,
--   $$\Pr\Big[\ \forall u \in V:\ |B(u)| \le C\, n^{1/k}\,(\lfloor \log_2 n\rfloor + 1)\ \Big] \ \ge\ 1 - n^{-c}.$$
--
--   This is the bunch-size bound $|B(u)| = O(n^{1/k}\log n)$ with high probability, the only place where the randomness of the hierarchy is used; it drives the time and space bounds of Theorem 1.
--
--   **Formalization Note** "With high probability" is read as: for every $c$, probability at least $1-n^{-c}$, with the constant chosen after $c$. The bound is asserted simultaneously for all vertices.
--
--   Differences from the source:
--   - reading: "with high probability" → for every c ∈ ℕ there is C with probability at least 1 − n^{−c}, C chosen after c and before the graph, k and v₀; reason: the conventional strongest reading of an unpinned "w.h.p."; the page prints no failure probability
--   - reading: |B(u)| = O(n^{1/k} log n) for a vertex u → the bound for all vertices u simultaneously; reason: for each u separately is the same statement with c replaced by c + 1, by a union bound over the n vertices
--   - encoding: O(n^{1/k} log n) → C · n^{1/k} · (⌊log₂ n⌋ + 1); reason: ⌊log₂ n⌋ + 1 is positive at n = 1 and within a factor 2 of log₂ n for n ≥ 2
--   - generalization: k ≤ log n (footnote 1, p.1) → every k ≥ 1; reason: the source case k ≤ log n is an instance
--   - generalization: an undirected graph G = (V, E) with positive real edge weights → an edge list on Fin n with positive real weights; parallel edges and loops allowed; reason: every weighted graph is an instance; a loop never shortens a walk and a parallel edge only adds walks
--   - encoding: G is connected → Connected G: n ≥ 1 and every two vertices are joined by a walk; reason: a connected graph has a vertex; no instance of the source is excluded
-- source:
--   Chechik, Kadria, Lifshitz, Roditty, Reading between the levels: new tools for the Thorup–Zwick hierarchy and their applications, arXiv:2611.01297 (held file sha256 dfeca900…), Lemma 4, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_TZLevelsADO_sampledA

open MeasureTheory

namespace TZLevelsADO

/-- S. Chechik, A. Kadria, G. Lifshitz, L. Roditty, *Reading between the levels*, arXiv:2611.01297
(held file sha256 dfeca900…), Lemma 4 (Section 3.5 in [TZ05]), p.7 (PDF p.8):
"|B(u)| = O(n^{1/k} log n) = Õ(n^{1/k}) with high probability."

**Formalization Note.**
* The probability is over the sampling of §2, p.7 (`coinLaw`): one independent coin per (level, vertex),
  `true` with probability `n^{−1/k}`, and the fixed vertex `v₀` added to `A_1, …, A_{k−1}`
  (`sampledHierarchy`). The bunch of the sampled hierarchy does not depend on the pivot choice.
* "With high probability" is read as: for every `c ∈ ℕ` the bound holds with probability at least
  `1 − n^{−c}`, with the constant `C` of the `O(·)` chosen after `c` and before the graph, `k` and `v₀`.
* The bound holds simultaneously for all vertices `u` (for each `u` separately is the same statement
  up to replacing `c` by `c + 1`, by a union bound over the `n` vertices).
* `log n` is `⌊log₂ n⌋ + 1`, which is positive at `n = 1`.
* Every `k ≥ 1` is allowed; the page assumes `k ≤ log n` (footnote 1, p.1). -/
theorem lemma_4 :
    ∀ c : ℕ, ∃ C : ℕ, ∀ (G : Graph), G.PosWeights → G.Connected →
      ∀ (k : ℕ) (hk : 0 < k) (v₀ : Fin G.n),
        ENNReal.ofReal (1 - (G.n : ℝ) ^ (-(c : ℝ))) ≤
          coinLaw G.n k {ω | ∀ u : Fin G.n,
            ((bunch (sampledHierarchy G k hk v₀ ω) u).card : ℝ) ≤
              C * (G.n : ℝ) ^ ((1 : ℝ) / k) * ((Nat.log 2 G.n : ℝ) + 1)} := by sorry

end TZLevelsADO
