-- Prove2me | Theorems.Thm_ShiAuthentication_BA_Supplement_lemma_4_9
-- name    : ShiAuthentication.BA.Supplement.lemma_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:22:45.492727+00:00
-- url     : https://prove2.me/theorems/c16884b9-a5fc-43d0-9326-0bbdcf08628b
-- title:
--   Lemma 4.9 — edge lower bound from the $r$-set cut condition
-- statement:
--   Let $G$ be a loopless digraph on $n$ vertices and let $r$ be an integer with $1\le r\le n/3$. Suppose every ordered pair of disjoint $r$-sets $X,Y$ has an edge from $X$ to $Y$. Then:
--
--   1. there is an absolute constant $c>0$ (the same for all $n$, $r$ and $G$) with
--   $$|E(G)|\ \ge\ c\cdot\min\Big\{n^2,\ \frac{n^2}{r}\ln\frac{en}{r}\Big\};$$
--   2. if $r=1$, then $G$ is complete and $|E(G)|=n(n-1)$;
--   3. if $r\ge 2$, then
--   $$\frac{|E(G)|}{n}+1\ \ge\ (n-r+1)\Big[1-\Big(\frac{r-1}{n}\Big)^{1/r}\Big].\tag{2}$$
--
--   This is the lower-bound half of the authentication complexity of agreement: combined with the necessary cut condition of Lemma 4.8 it bounds the number of edges of every feasible graph.
--
--   Differences from the source:
--   - encoding: |E(G)| = Ω(min{n², (n²/r) ln(en/r)}) → ∃ c > 0 before ∀ n r G, with c · min{…} ≤ |E(G)|; reason: the Ω ranges over the two parameters n, r; a constant fixed before them is the uniform reading supported by the proof
--   - encoding: 1 ≤ r ≤ n/3 (integer r) → 1 ≤ r and 3 * r ≤ n in ℕ; reason: equivalent for natural numbers; in the r = 1 clause this is 3 ≤ n
-- source:
--   Kecheng Shi, STOC 2027 submission #203 (October 2026), Lemma 4.9, pp. 22–23

import Definitions.Def_ShiAuthentication_BA_Supplement_Complexity

set_option autoImplicit false

namespace ShiAuthentication.BA.Supplement

/-- **Lemma 4.9**, pp. 22–23. Let `G` be a loopless digraph on `n` vertices and `r` an integer
with `1 ≤ r ≤ n/3` such that every ordered pair of disjoint `r`-sets `X, Y` has an edge from
`X` to `Y`. Then
(1) `|E(G)| = Ω(min{n², (n²/r) ln(en/r)})`, with one absolute constant `c > 0` for all `n, r, G`;
(2) for `r = 1`, `G` is complete and `|E(G)| = n(n − 1)`;
(3) for `r ≥ 2`, `|E(G)|/n + 1 ≥ (n − r + 1)[1 − ((r − 1)/n)^{1/r}]` (inequality (2)). -/
theorem lemma_4_9 :
    (∃ c : ℝ, 0 < c ∧ ∀ (n r : ℕ) (G : AuthGraph n), 1 ≤ r → 3 * r ≤ n → CutCondition G r r →
      c * min ((n : ℝ) ^ 2) ((n : ℝ) ^ 2 / r * Real.log (Real.exp 1 * n / r)) ≤ edgeCount G) ∧
    (∀ (n : ℕ) (G : AuthGraph n), 3 ≤ n → CutCondition G 1 1 →
      G.IsComplete ∧ edgeCount G = n * (n - 1)) ∧
    (∀ (n r : ℕ) (G : AuthGraph n), 2 ≤ r → 3 * r ≤ n → CutCondition G r r →
      ((n - r + 1 : ℕ) : ℝ) * (1 - (((r : ℝ) - 1) / n) ^ ((1 : ℝ) / r)) ≤
        (edgeCount G : ℝ) / n + 1) := by sorry

end ShiAuthentication.BA.Supplement
