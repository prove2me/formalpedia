-- Prove2me | Theorems.Thm_PredAdvice_Supplement_theorem_3_1
-- name    : PredAdvice.Supplement.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:33:11.796961+00:00
-- url     : https://prove2.me/theorems/51682ab5-9f54-4e54-a78d-c746474fe23e
-- title:
--   Theorem 3.1 — edge-centered three-hopsets of size $O(n^2(\log D/D+1/D+D/2^L+LD^2/RS(n)))$
-- statement:
--   Let $RS(n)$ be the Ruzsa–Szemerédi function and logarithms base $2$. There is an absolute constant $C$ such that for all integers $2\le D\le n$ and $L\ge1$, every directed unweighted $n$-vertex graph $G$ has an exact edge-centered three-hopset $H$ with
--
--   $$|H|\le C\,n^2\Big(\frac{\log D}{D}+\frac1D+\frac{D}{2^L}+\frac{LD^2}{RS(n)}\Big).$$
--
--   This is the parametrized form behind Theorem 1.2: the four terms come from covering pairs with many shortest-path vertices by sampling, from the colourings separating the remaining pairs, and from the induced-matching hops. Choosing $D$ and $L$ as functions of $RS(n)$ yields Theorem 1.2.
--
--   **Formalization Note** The constant $C$ is chosen before $n$, $D$, $L$ and the graph.
--
--   Differences from the source:
--   - reading: O(n²(log D/D + 1/D + D/2^L + LD²/RS(n))) for all 2 ≤ D ≤ n, L ≥ 1 and every graph → ∃ C, ∀ n D L with 2 ≤ D ≤ n and 1 ≤ L, ∀ G : Digraph (Fin n), ∃ edge-centered three-hopset H with size ≤ C·n²(…); reason: O unfolded with a constant independent of n, D, L and G
--   - encoding: directed unweighted n-vertex graph → Mathlib Digraph (Fin n) (loops allowed); reason: a loop never lies on a shortest path, so distances and hopsets are unchanged
--   - encoding: hopset size |H|, diagonal edges free (p.10) → number of off-diagonal pairs of a finite hop set; a hop between an unreachable pair is allowed but has weight ⊤ and can lie on no exact route; reason: the paper's convention; an unreachable hop only adds to the size
--   - reading: edge-centered property, “u → x → y → v … has total weight dist_G(u, v)” (p.5) → explicit clause dist(u,x) + 1_{x≠y} + dist(y,v) = dist(u,v) with (x,y) an edge of G or x = y; reason: an edge between distinct vertices has weight 1 = dist(x,y), so the clause is the page's total-weight condition written out
-- source:
--   Kopelowitz, Korin, Roditty, Using Small Advice to Compress the Predecessor Matrix, STOC 2027 submission (manuscript sha256 0ae8a68d…), Theorem 3.1, p.11 (pdf p.11); proof §3.4, p.14

import Mathlib
import Definitions.Def_PredAdvice_RS
import Definitions.Def_PredAdvice_Supplement_IsExactHopset

set_option autoImplicit false

namespace PredAdvice

namespace Supplement

/-- **Theorem 3.1** (Kopelowitz, Korin, Roditty, *Using Small Advice to Compress the Predecessor Matrix*, STOC 2027 submission (manuscript sha256 0ae8a68d…), §3, p.11; proof §3.4, p.14). For every integers `2 ≤ D ≤ n` and
`L ≥ 1`, every directed unweighted `n`-vertex graph has an exact edge-centered 3-hopset of size
`O(n²(log D/D + 1/D + D/2^L + LD²/RS(n)))`.

**Formalization Note** The `O` constant `C` is absolute: chosen before `n`, `D`, `L` and the
graph. The term `D/2^L` is printed so (from `n²D2^{−L}` in eq. (5)). Logarithms are base 2. -/
theorem theorem_3_1 :
    ∃ C : ℝ, ∀ n D L : ℕ, 2 ≤ D → D ≤ n → 1 ≤ L → ∀ G : Digraph (Fin n),
      ∃ H : Finset (Fin n × Fin n), IsEdgeCentered3Hopset G H ∧
        (hopsetSize H : ℝ) ≤ C * ((n : ℝ) ^ 2 * (Real.logb 2 D / D + 1 / D + D / 2 ^ L +
          L * (D : ℝ) ^ 2 / RS n)) := by sorry

end Supplement

end PredAdvice
