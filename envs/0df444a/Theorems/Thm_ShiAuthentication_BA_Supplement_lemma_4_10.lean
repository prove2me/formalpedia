-- Prove2me | Theorems.Thm_ShiAuthentication_BA_Supplement_lemma_4_10
-- name    : ShiAuthentication.BA.Supplement.lemma_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:23:35.045415+00:00
-- url     : https://prove2.me/theorems/40bbcb23-e3bc-4365-aee0-75c548d9f3b9
-- title:
--   Lemma 4.10 — sparse digraphs with the $\lceil r/2\rceil$-to-$r$ cut condition
-- statement:
--   Let $N$ and $r$ be integers with $2\le r\le N/3$ and put $k=\lceil r/2\rceil$. There is an $N$-vertex loopless digraph $G$ with an edge from every $k$-set to every disjoint $r$-set such that
--   $$|E(G)|\le C\min\Big\{N^2,\ \frac{N^2}{r}\ln\frac{eN}{r}\Big\},\qquad \max_v |K_v|\le C\min\Big\{N,\ \frac{N}{r}\ln\frac{eN}{r}\Big\},$$
--   where $C>0$ is an absolute constant, the same for all $N$ and $r$, and $K_v$ is the set of in-neighbours of $v$.
--
--   This is the construction behind the upper bounds of Theorem 4.11: by Lemma 4.8 such a graph supports Byzantine agreement, with total cost and per-party cost both of optimal order.
--
--   Differences from the source:
--   - encoding: O(min{N², (N²/r) ln(eN/r)}) edges and maximum indegree O(min{N, (N/r) ln(eN/r)}) → ∃ C > 0 before ∀ N r, bounding both quantities by C · min{…}; reason: the O ranges over N and r; one constant for both bounds is equivalent to two (take the larger)
--   - encoding: k = ⌈r/2⌉ → (r + 1) / 2 in ℕ; reason: equal for every natural r
-- source:
--   Kecheng Shi, STOC 2027 submission #203 (October 2026), Lemma 4.10, pp. 23–24

import Definitions.Def_ShiAuthentication_BA_Supplement_Complexity

set_option autoImplicit false

namespace ShiAuthentication.BA.Supplement

/-- **Lemma 4.10**, p. 23. There is an absolute constant `C > 0` such that for all integers
`N, r` with `2 ≤ r ≤ N/3`, with `k = ⌈r/2⌉` (written `(r + 1) / 2`), some loopless digraph on
`N` vertices has an edge from every `k`-set to every disjoint `r`-set, at most
`C · min{N², (N²/r) ln(eN/r)}` edges and maximum indegree at most
`C · min{N, (N/r) ln(eN/r)}`. -/
theorem lemma_4_10 :
    ∃ C : ℝ, 0 < C ∧ ∀ N r : ℕ, 2 ≤ r → 3 * r ≤ N →
      ∃ G : AuthGraph N, CutCondition G ((r + 1) / 2) r ∧
        (edgeCount G : ℝ) ≤
          C * min ((N : ℝ) ^ 2) ((N : ℝ) ^ 2 / r * Real.log (Real.exp 1 * N / r)) ∧
        (maxIndegree G : ℝ) ≤
          C * min (N : ℝ) ((N : ℝ) / r * Real.log (Real.exp 1 * N / r)) := by sorry

end ShiAuthentication.BA.Supplement
