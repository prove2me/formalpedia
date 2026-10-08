-- Prove2me | Theorems.Thm_RobinsonFP_Convergence_eq3
-- name    : RobinsonFP.Convergence.eq3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:39:21.283301+00:00
-- url     : https://prove2.me/theorems/8c93a0c9-a634-4fc9-b574-6cb021ac8a50
-- title:
--   (3), proof of Lemma 4 — if some row or column is not eligible in (s, s+t*), the gap grows by less than ½εt*
-- statement:
--   Let $A = (a_{ij})$ be a real $m \times n$ matrix with $m, n \ge 1$, let $\varepsilon > 0$, and let $t^*$ be a nonnegative integer with the following property: for every submatrix $A'$ obtained from $A$ by deleting one row or one column (and still having at least one row and one column), every vector system $(U', V')$ for $A'$ satisfies
--   $$\max V'(t) - \min U'(t) < \tfrac12 \varepsilon t \qquad\text{whenever } t \ge t^* .$$
--   Let $(U, V)$ be a vector system for $A$ and $s$ a nonnegative integer. If some row or some column of $A$ is not eligible in the interval $(s, s+t^*)$, then
--   $$\max V(s+t^*) - \min U(s+t^*) \;<\; \max V(s) - \min U(s) + \tfrac12 \varepsilon t^* .$$
--
--   This is the induction step of the proof of Lemma 4: over a window in which some pure strategy is never a best reply, the vector system behaves like one for a smaller matrix, so the gap grows by less than $\tfrac12\varepsilon t^*$.
--
--   **Formalization Note** The paper chooses $t^*$ for all submatrices $A'$ of $A$; we assume the bound only for the submatrices obtained by deleting a single row or a single column, the ones its argument uses, so our statement is at least as strong. The paper writes out the row case only ("Suppose, for example, that the $k$-th row is not eligible", p. 300); the statement covers both cases, as (3) does. Deleting row $k$ gives the rows indexed by $\{i \ne k\}$, and the bound is assumed only when this index set is nonempty, because $\max$ needs at least one component; an ineligible row $k$ forces another row to exist, so nothing is lost.
-- source:
--   Robinson, An Iterative Method of Solving a Game, Ann. of Math. 54(2) (1951), p. 299, display (3) in the proof of Lemma 4

import Mathlib
import Definitions.Def_RobinsonFP_Convergence_VectorSystem

namespace RobinsonFP.Convergence

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Robinson (1951), p. 299, display (3) in the proof of Lemma 4: let `t*` be such that every
vector system `(U', V')` of a submatrix `A'` obtained by deleting one row or one column of `A`
satisfies `max V'(t) − min U'(t) < ½εt` for `t ≥ t*`. If some row or some column of `A` is not
eligible in `(s, s + t*)` for the vector system `(U, V)`, then
`max V(s+t*) − min U(s+t*) < max V(s) − min U(s) + ½εt*`. -/
theorem eq3 [DecidableEq ι] [DecidableEq κ] [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ)
    (ε : ℝ) (hε : 0 < ε) (tstar : ℕ)
    (hrowIH : ∀ k : ι, ∀ (_ : Nonempty {i // i ≠ k}) (U' : ℕ → κ → ℝ)
      (V' : ℕ → {i // i ≠ k} → ℝ),
      IsVectorSystem (A.submatrix Subtype.val id) U' V' →
        ∀ t : ℕ, tstar ≤ t → vmax (V' t) - vmin (U' t) < ε / 2 * t)
    (hcolIH : ∀ k : κ, ∀ (_ : Nonempty {j // j ≠ k}) (U' : ℕ → {j // j ≠ k} → ℝ)
      (V' : ℕ → ι → ℝ),
      IsVectorSystem (A.submatrix id Subtype.val) U' V' →
        ∀ t : ℕ, tstar ≤ t → vmax (V' t) - vmin (U' t) < ε / 2 * t)
    (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ) (hUV : IsVectorSystem A U V) (s : ℕ)
    (hnot : (∃ i, ¬ RowEligible V i s (s + tstar)) ∨ (∃ j, ¬ ColEligible U j s (s + tstar))) :
    vmax (V (s + tstar)) - vmin (U (s + tstar)) <
      vmax (V s) - vmin (U s) + ε / 2 * tstar := by sorry

end RobinsonFP.Convergence
