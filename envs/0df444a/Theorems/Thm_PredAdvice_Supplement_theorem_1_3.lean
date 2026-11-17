-- Prove2me | Theorems.Thm_PredAdvice_Supplement_theorem_1_3
-- name    : PredAdvice.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:31:03.883221+00:00
-- url     : https://prove2.me/theorems/ba27ceff-95b7-4bdc-abb8-5cb3a9479aa6
-- title:
--   Theorem 1.3 — every exact 4-hopset of some $n$-vertex graph has $\Omega(n^2/RS(n))$ hops
-- statement:
--   Let $RS(n)$ be the Ruzsa–Szemerédi function. There are a constant $c>0$ and a threshold $N_0$ such that for every $n\ge N_0$:
--
--   1. some undirected unweighted graph on $n$ vertices has the property that every exact $4$-hopset $H$ for it satisfies $|H|\ge c\,n^2/RS(n)$;
--   2. some directed unweighted graph on $n$ vertices has the same property for directed hopsets.
--
--   In the paper's notation, for every sufficiently large $n$,
--
--   $$\mathrm{Hop}_4(n)=\Omega\Big(\frac{n^2}{RS(n)}\Big).$$
--
--   Together with Theorem 1.2 it shows that $\mathrm{Hop}_4(n)$, $\mathrm{Hop}_3(n)$ and $\mathrm{Hop}_{ec3}(n)$ all lie between $n^2/RS(n)$ and $n^2/RS(n)^{1/3}$ up to constant and logarithmic factors (Corollary 1.4).
--
--   **Formalization Note** Every finite set of hops is quantified, including hops between unreachable pairs and diagonal hops; only off-diagonal hops are counted. Footnotes 4 and 16 say the lower bound holds for undirected and for directed graphs, so both clauses are stated.
--
--   Differences from the source:
--   - reading: for every sufficiently large n, Hop₄(n) = Ω(n²/RS(n)) → ∃ c > 0, ∃ N₀, ∀ n ≥ N₀, ∃ graph on Fin n such that every exact 4-hopset H has size ≥ c·n²/RS(n); reason: the definition of the max/min, of Ω and of 'sufficiently large', unfolded
--   - encoding: unweighted directed / undirected n-vertex graphs → Mathlib Digraph (Fin n) (loops allowed) / SimpleGraph (Fin n); undirected distances are those of the symmetric digraph, undirected hops are unordered pairs (Sym2); reason: a loop never lies on a shortest path, so distances and hopsets are unchanged; footnote 4 reads an undirected edge as two opposite directed edges
--   - encoding: hopset size |H|, diagonal edges free (p.10) → number of off-diagonal pairs of a finite hop set; a hop between an unreachable pair is allowed but has weight ⊤ and can lie on no exact route; reason: the paper's convention; an unreachable hop only adds to the size
-- source:
--   Kopelowitz, Korin, Roditty, Using Small Advice to Compress the Predecessor Matrix, STOC 2027 submission (manuscript sha256 0ae8a68d…), Theorem 1.3, p.5 (pdf p.5); proof §7.2, p.28; footnotes 4 (p.4) and 16 (p.25)

import Mathlib
import Definitions.Def_PredAdvice_RS
import Definitions.Def_PredAdvice_Supplement_IsExactHopset

set_option autoImplicit false

namespace PredAdvice

namespace Supplement

/-- **Theorem 1.3** (four-hopset lower bound; Kopelowitz, Korin, Roditty, *Using Small Advice to Compress the Predecessor Matrix*, STOC 2027 submission (manuscript sha256 0ae8a68d…), §1.2, p.5; proof §7.2, p.28). For every
sufficiently large `n`, `Hop₄(n) = Ω(n²/RS(n))`.

**Formalization Note**
* `Ω` is pinned: there are `c > 0` and `N₀` such that for every `n ≥ N₀` some graph on exactly
  `n` vertices has the property that every exact 4-hopset `H` (any finite set of hops, reachable
  or not) has at least `c · n²/RS(n)` off-diagonal hops.
* Footnote 4 (p.4) and footnote 16 (p.25): the lower bound holds for undirected graphs (unordered
  hops) and for directed graphs; both clauses are stated. -/
theorem theorem_1_3 :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (∃ G : SimpleGraph (Fin n), ∀ H : Finset (Sym2 (Fin n)), IsExactHopsetU G 4 H →
        c * ((n : ℝ) ^ 2 / RS n) ≤ (hopsetSizeU H : ℝ)) ∧
      (∃ G : Digraph (Fin n), ∀ H : Finset (Fin n × Fin n), IsExactHopset G 4 H →
        c * ((n : ℝ) ^ 2 / RS n) ≤ (hopsetSize H : ℝ)) := by sorry

end Supplement

end PredAdvice
