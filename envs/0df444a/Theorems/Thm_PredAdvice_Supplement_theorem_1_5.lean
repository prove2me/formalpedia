-- Prove2me | Theorems.Thm_PredAdvice_Supplement_theorem_1_5
-- name    : PredAdvice.Supplement.theorem_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:31:36.179379+00:00
-- url     : https://prove2.me/theorems/72f06271-9a84-47b4-a1e1-99b8747ae966
-- title:
--   Theorem 1.5 — exact $3k$-hopsets of size $O_k(n^2(1+\log RS(n))/RS(n)^{k/(2k+1)})$
-- statement:
--   Let $RS(n)$ be the Ruzsa–Szemerédi function and logarithms base $2$. For every integer $k\ge1$ there are constants $C_k$ and $N_k$, depending on $k$ only, such that for every $n\ge N_k$, every unweighted $n$-vertex graph — directed or undirected — has an exact $3k$-hopset $H$ with
--
--   $$|H|\le C_k\,\frac{n^2\,(1+\log RS(n))}{RS(n)^{k/(2k+1)}} .$$
--
--   In the paper's notation, $\mathrm{Hop}_{3k}(n)=O_k\big(n^2(1+\log RS(n))/RS(n)^{k/(2k+1)}\big)$ (eq. (1)). For $k=1$ this is the bound of Theorem 1.2; the exponent $k/(2k+1)$ tends to $1/2$ as the hopbound grows.
--
--   **Formalization Note** Footnote 4 says the bound applies to directed and undirected graphs, so both clauses are stated.
--
--   Differences from the source:
--   - reading: for sufficiently large n and constant k ≥ 1, Hop_{3k}(n) = O_k(f_k(n)) → ∀ k ≥ 1, ∃ C N₀, ∀ n ≥ N₀, ∀ graph on Fin n, ∃ exact 3k-hopset H with size ≤ C·f_k(n); reason: the definition of the max/min, of O_k and of 'sufficiently large', unfolded; the constants depend on k only
--   - encoding: unweighted directed / undirected n-vertex graphs → Mathlib Digraph (Fin n) (loops allowed) / SimpleGraph (Fin n); undirected distances are those of the symmetric digraph, undirected hops are unordered pairs (Sym2); reason: a loop never lies on a shortest path, so distances and hopsets are unchanged; footnote 4 reads an undirected edge as two opposite directed edges
--   - encoding: hopset size |H|, diagonal edges free (p.10) → number of off-diagonal pairs of a finite hop set; a hop between an unreachable pair is allowed but has weight ⊤ and can lie on no exact route; reason: the paper's convention; an unreachable hop only adds to the size
-- source:
--   Kopelowitz, Korin, Roditty, Using Small Advice to Compress the Predecessor Matrix, STOC 2027 submission (manuscript sha256 0ae8a68d…), Theorem 1.5, eq. (1), p.6 (pdf p.6); proof §3.5, p.16; footnote 4, p.4

import Mathlib
import Definitions.Def_PredAdvice_RS
import Definitions.Def_PredAdvice_Supplement_IsExactHopset

set_option autoImplicit false

namespace PredAdvice

namespace Supplement

/-- **Theorem 1.5** (fixed hopbound tradeoff; Kopelowitz, Korin, Roditty, *Using Small Advice to Compress the Predecessor Matrix*, STOC 2027 submission (manuscript sha256 0ae8a68d…), §1.2, p.6, eq. (1); proof §3.5, p.16). For
any sufficiently large natural `n` and constant integer `k ≥ 1`,
`Hop_{3k}(n) = O_k(n²(1 + log RS(n))/RS(n)^{k/(2k+1)})`.

**Formalization Note**
* `O_k` and "sufficiently large": for every `k ≥ 1` there are `C` and `N₀` (depending on `k`
  only) such that for every `n ≥ N₀` every graph on `Fin n` has an exact `3k`-hopset with at
  most `C · n²(1 + log₂ RS(n))/RS(n)^{k/(2k+1)}` off-diagonal hops.
* Footnote 4 (p.4): directed and undirected clauses. -/
theorem theorem_1_5 :
    ∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (∀ G : Digraph (Fin n), ∃ H : Finset (Fin n × Fin n), IsExactHopset G (3 * k) H ∧
        (hopsetSize H : ℝ) ≤ C * ((n : ℝ) ^ 2 * (1 + Real.logb 2 (RS n)) /
          RS n ^ ((k : ℝ) / (2 * k + 1)))) ∧
      (∀ G : SimpleGraph (Fin n), ∃ H : Finset (Sym2 (Fin n)), IsExactHopsetU G (3 * k) H ∧
        (hopsetSizeU H : ℝ) ≤ C * ((n : ℝ) ^ 2 * (1 + Real.logb 2 (RS n)) /
          RS n ^ ((k : ℝ) / (2 * k + 1)))) := by sorry

end Supplement

end PredAdvice
