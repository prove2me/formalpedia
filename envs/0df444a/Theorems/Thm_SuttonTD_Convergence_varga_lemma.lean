-- Prove2me | Theorems.Thm_SuttonTD_Convergence_varga_lemma
-- name    : SuttonTD.Convergence.varga_lemma
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:24:13.835039+00:00
-- url     : https://prove2.me/theorems/78dd1e86-a1d3-4ab7-9a4e-eb7b888904d6
-- title:
--   Lemma (Varga) — symmetric, strictly diagonally dominant, positive diagonal ⇒ positive definite
-- statement:
--   Let $A$ be a real symmetric matrix that is strictly diagonally dominant ($|a_{ii}|>\sum_{j\ne i}|a_{ij}|$ for every $i$) and has positive diagonal entries. Then $A$ is positive definite:
--
--   $$y^\top A\,y>0\qquad\text{for every real } y\neq0 .$$
--
--   **Formalization Note** The standard definition of strict diagonal dominance is used. The paper's own definition on p. 27 (weak inequality in every row, strict in at least one) makes the Lemma false; see the definition `StrictlyDiagDominant`.
-- source:
--   Sutton (1988), Machine Learning 3:9–44, §4.1, Lemma, p. 27 (PDF p. 19), citing Varga (1962), p. 23

import Definitions.Def_SuttonTD_Convergence_IsPosDefReal
import Definitions.Def_SuttonTD_Convergence_StrictlyDiagDominant

namespace SuttonTD.Convergence

/-- **Lemma** (Sutton 1988, §4.1, p. 27, PDF p. 19, citing Varga 1962, p. 23): "If `A` is a real,
symmetric, and strictly diagonally dominant matrix with positive diagonal entries, then `A` is
positive definite."

Formalization Note: strict diagonal dominance is the standard notion (`|a_ii| > ∑_{j≠i} |a_ij|`
in every row, `StrictlyDiagDominant`). The paper's p. 27 definition (weak inequality in every row,
strict in at least one) makes the lemma false — `[[1,−1,0],[−1,1,0],[0,0,1]]` — and is not used.
Positive definite is the paper's footnote 6 (`IsPosDefReal`). -/
theorem varga_lemma {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (hsymm : A.IsSymm) (hdom : StrictlyDiagDominant A) (hdiag : ∀ i, 0 < A i i) :
    IsPosDefReal A := by sorry

end SuttonTD.Convergence
