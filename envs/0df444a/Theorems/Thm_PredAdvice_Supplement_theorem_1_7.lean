-- Prove2me | Theorems.Thm_PredAdvice_Supplement_theorem_1_7
-- name    : PredAdvice.Supplement.theorem_1_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:32:15.546247+00:00
-- url     : https://prove2.me/theorems/07617639-951b-48b4-92f3-8114aade6ea5
-- title:
--   Theorem 1.7 — exact 2-hopsets of graphs with $O(n^{1+1/k})$ edges need $\Omega_k(n^2/RS(n^{1/k})^k)$ hops
-- statement:
--   Let $RS$ be the Ruzsa–Szemerédi function. For every integer $k\ge2$ there are constants $C_k$ and $c_k>0$, depending on $k$ only, such that for infinitely many $n$ there is an undirected unweighted graph $G$ on $n$ vertices with at most $C_k\,n^{1+1/k}$ edges for which every exact $2$-hopset $H$ satisfies
--
--   $$|H|\ge c_k\,\frac{n^2}{RS(\lfloor n^{1/k}\rfloor)^{k}} .$$
--
--   In the paper's notation, $\mathrm{Hop}_2\big(n,O(n^{1+1/k})\big)=\Omega_k\big(n^2/RS(n^{1/k})^k\big)$, where $\mathrm{Hop}_2(n,m)$ is the maximum over undirected unweighted graphs with $n$ vertices and at most $m$ edges of the minimum size of an exact 2-hopset. Since $q/RS(q)=\Omega(r_3(q))$, this recovers the earlier bound $\Omega_k(n\,r_3(n^{1/k})^k)$ in terms of progression-free sets.
--
--   **Formalization Note** "Infinitely many $n$" is: for every $N$ there is such an $n\ge N$. $RS$ takes a natural argument, so $n^{1/k}$ is read as $\lfloor n^{1/k}\rfloor$; by the constant-scale stability of $RS$ (§2) this changes the bound only by a factor depending on $k$.
--
--   Differences from the source:
--   - reading: RS(n^{1/k}), with n^{1/k} not an integer in general → RS(⌊n^{1/k}⌋₊), the floor of the real k-th root; reason: RS is defined on naturals; by constant-scale stability (§2, p.10) any natural argument between ⌊n^{1/k}⌋ and ⌈n^{1/k}⌉ gives the same bound up to a factor depending on k
--   - reading: for infinitely many n, Hop₂(n, O(n^{1+1/k})) = Ω_k(n²/RS(n^{1/k})^k) → ∀ k ≥ 2, ∃ C c > 0, ∀ N, ∃ n ≥ N, ∃ undirected G on Fin n with |E(G)| ≤ C·n^{1+1/k} such that every exact 2-hopset H has size ≥ c·n²/RS(⌊n^{1/k}⌋)^k; reason: the definition of Hop₂(n, m), of O and Ω_k and of 'infinitely many', unfolded
--   - encoding: undirected unweighted graph with at most m edges → SimpleGraph (Fin n), edges counted by edgeSet.ncard, unordered hops (Sym2); reason: Hop_D(n, m) is defined over undirected graphs (p.4)
--   - encoding: hopset size |H|, diagonal edges free (p.10) → number of off-diagonal pairs of a finite hop set; a hop between an unreachable pair is allowed but has weight ⊤ and can lie on no exact route; reason: the paper's convention; an unreachable hop only adds to the size
-- source:
--   Kopelowitz, Korin, Roditty, Using Small Advice to Compress the Predecessor Matrix, STOC 2027 submission (manuscript sha256 0ae8a68d…), Theorem 1.7, p.6 (pdf p.6); Hop_D(n, m), p.4; proof §7.1, p.27

import Mathlib
import Definitions.Def_PredAdvice_RS
import Definitions.Def_PredAdvice_Supplement_IsExactHopset

set_option autoImplicit false

namespace PredAdvice

namespace Supplement

/-- **Theorem 1.7** (two-hopset lower bound; Kopelowitz, Korin, Roditty, *Using Small Advice to Compress the Predecessor Matrix*, STOC 2027 submission (manuscript sha256 0ae8a68d…), §1.2, p.6; proof §7.1, p.27). For every fixed
integer `k ≥ 2` and infinitely many `n`, `Hop₂(n, O(n^{1+1/k})) = Ω_k(n²/RS(n^{1/k})^k)`.

**Formalization Note**
* `Hop₂(n, m)` is over undirected graphs with `n` vertices and at most `m` edges (p.4), so the
  statement is about `SimpleGraph (Fin n)` and unordered hops.
* For every `k ≥ 2` there are constants `C` (the edge bound `O(n^{1+1/k})`) and `c > 0`, depending
  on `k` only, such that for every `N` there are `n ≥ N` and an undirected graph on `Fin n` with at
  most `C n^{1+1/k}` edges all of whose exact 2-hopsets have at least `c n²/RS(⌊n^{1/k}⌋)^k`
  off-diagonal hops.
* `RS` takes a natural argument, so `n^{1/k}` is read as `⌊n^{1/k}⌋` (floor of the real root). By the
  constant-scale stability of `RS` (§2, p.10) any natural argument between `⌊n^{1/k}⌋` and
  `⌈n^{1/k}⌉` changes the bound by a factor depending on `k` only. -/
theorem theorem_1_7 :
    ∀ k : ℕ, 2 ≤ k → ∃ C c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∃ G : SimpleGraph (Fin n), (G.edgeSet.ncard : ℝ) ≤ C * (n : ℝ) ^ (1 + 1 / (k : ℝ)) ∧
        ∀ H : Finset (Sym2 (Fin n)), IsExactHopsetU G 2 H →
          c * ((n : ℝ) ^ 2 / RS ⌊(n : ℝ) ^ (1 / (k : ℝ))⌋₊ ^ k) ≤ (hopsetSizeU H : ℝ) := by sorry

end Supplement

end PredAdvice
