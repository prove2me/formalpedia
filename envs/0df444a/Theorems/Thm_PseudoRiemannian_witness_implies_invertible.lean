-- Prove2me | Theorems.Thm_PseudoRiemannian_witness_implies_invertible
-- name    : PseudoRiemannian.witness_implies_invertible
-- status  : Open
-- author  : @LG
-- created : 2026-11-27T02:29:06.981458+00:00
-- url     : https://prove2.me/theorems/3f22a512-0eb3-461e-9e30-162ba1e70693
-- title:
--   A signature witness makes the metric matrix invertible
-- statement:
--   **A signature witness makes the metric invertible — entry rung.**
--
--   Let `s` be a signature vector (entries $\pm 1$), let `B` be an invertible $n \times n$ real matrix (`IsUnit B.det`), and let the metric matrix at `x` be congruent to the signature diagonal:
--
--   $$B^{T}\, g(x)\, B \;=\; \mathrm{diag}(s).$$
--
--   **Conclusion:** the metric matrix is invertible: `IsUnit (g x).det`.
--
--   In words: the pointwise half of the source's "everywhere nondegenerate". The computation: $\det(B)^2 \det(g(x)) = \det(B^{T} g(x) B) = \det(\mathrm{diag}\, s) = \prod_i s_i = \pm 1$, and since $\det(B)^2 \neq 0$ also $\det(g(x)) \neq 0$. Invertibility of $g(x)$ is the hinge from which nondegeneracy (next rung) follows.
--
--   **Formalization note.** `Matrix.det_mul`, `Matrix.det_transpose`, `Matrix.det_diagonal` and `IsUnit` of real numbers; `hs` gives $\prod_i s_i = \pm 1 \neq 0$ by finite-product induction over the two cases. No smoothness or symmetry needed.
-- source:
--   Wikipedia, Pseudo-Riemannian manifold, https://en.wikipedia.org/wiki/Pseudo-Riemannian_manifold (source of the quoted statements, reproduced verbatim in the definition file) ('a metric tensor that is everywhere nondegenerate'); standard determinant algebra

import Mathlib
import Definitions.Def_PseudoRiemannian

namespace PseudoRiemannian

open Matrix
open scoped ContDiff

/-- Milestone: a signature witness makes the metric matrix invertible.  If
`B` is invertible and congruent the metric matrix `g x` to the signature
diagonal `diag s` (`Bᵀ (g x) B = diag s` with `s` taking values `± 1`), then
`g x` is invertible: `det(B)² det(g x) = det(diag s) = ∏ s i = ± 1 ≠ 0`.  This
is the algebraic core of the source's "everywhere nondegenerate": the carried
signature witness pins down nondegeneracy pointwise. -/
theorem witness_implies_invertible {n : ℕ} {g : Spc n → Matrix (Fin n) (Fin n) ℝ}
    {s : Fin n → ℝ} (hs : IsSignVec s) {x : Spc n} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : IsUnit B.det) (hcong : Bᵀ * g x * B = Matrix.diagonal s) :
    IsUnit (g x).det := by
  sorry

end PseudoRiemannian
