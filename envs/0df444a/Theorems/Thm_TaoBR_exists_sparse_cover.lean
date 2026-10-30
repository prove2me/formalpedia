-- Prove2me | Theorems.Thm_TaoBR_exists_sparse_cover
-- name    : TaoBR.exists_sparse_cover
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T17:07:16.29805+00:00
-- url     : https://prove2.me/theorems/3d067284-fe77-4071-9e2b-14630d076b98
-- title:
--   Lemma 3.3 — a union of c-cubes is covered by O(N|E|^{1/N}) sparse collections of balls of radius O(max(1, |E|)^{C^N})
-- statement:
--   For $n \ge 2$, every $c > 0$ and every sparseness constant $C_0$ there are constants $A$ and $C_1$ with the following property. If $E \subseteq \mathbf R^n$ is a finite union of $c$-cubes $k + [-c/2, c/2]^n$ centred at points $k \in \mathbf Z^n$, and $N \ge 1$, then there are at most $A N|E|^{1/N}$ collections of balls covering $E$. The $j$-th collection consists of closed balls of one radius $R_j$ with $1 \le R_j \le A\max(1, |E|)^{C_1^N}$, and their centres form a sparse collection with constant $C_0$.
--
--   *Formalization note.* The constants may depend on the prescribed sparseness constant, which is what Lemma 3.2 needs: the proof picks the radii $R_{k+1} = |E|^CR_k^C$ with $C$ large. The source gives no regime for its $O(|E|^{C^N})$, and the statement reads it as $A\max(1, |E|)^{C_1^N}$; the two differ only when $|E| < 1$, which happens only for $c < 1$. The conclusion $R_j \ge 1$ goes beyond the printed lemma; it matches the radii $R \ge 1$ of the localized estimate $R(p, \alpha)$ (`TaoBR.Restr`), which Lemma 3.2 extends to sparse unions of balls.
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 7, Lemma 3.3

import Mathlib
import Definitions.Def_TaoBR

open MeasureTheory Metric

namespace TaoBR

theorem exists_sparse_cover (n : ℕ) (hn : 2 ≤ n) (c : ℝ) (hc : 0 < c) (C₀ : ℝ) :
    ∃ A C₁ : ℝ, ∀ S : Set (E n), IsCubeUnion c S → ∀ N : ℕ, 1 ≤ N →
      ∃ (J : ℕ) (R : Fin J → ℝ) (M : Fin J → ℕ) (x : (j : Fin J) → Fin (M j) → E n),
        (J : ℝ) ≤ A * N * (volume S).toReal ^ (1 / (N : ℝ)) ∧
        (∀ j, 1 ≤ R j ∧ R j ≤ A * (max 1 (volume S).toReal) ^ (C₁ ^ N) ∧ IsSparse C₀ (R j) (x j)) ∧
        S ⊆ ⋃ (j) (i), closedBall (x j i) (R j) := by
  sorry

end TaoBR
