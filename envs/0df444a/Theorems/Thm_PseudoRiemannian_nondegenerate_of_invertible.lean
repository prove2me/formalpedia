-- Prove2me | Theorems.Thm_PseudoRiemannian_nondegenerate_of_invertible
-- name    : PseudoRiemannian.nondegenerate_of_invertible
-- status  : Open
-- author  : @LG
-- created : 2026-11-27T02:29:33.789161+00:00
-- url     : https://prove2.me/theorems/61b76a2d-48c3-41ef-ae9f-8e5a04d76bbf
-- title:
--   Nondegeneracy in the article's sense, from invertibility
-- statement:
--   **Nondegeneracy — the article's condition, from invertibility.**
--
--   Let the metric matrix at `x` be invertible: `IsUnit (g x).det`.
--
--   **Conclusion:** the pairing at `x` is nondegenerate in the article's exact sense — "there is no non-zero X in TpM such that g(X, Y) = 0 for all Y in TpM":
--
--   $$\forall\, u,\ \big(\forall\, v,\ \mathrm{pair}(g, x, u, v) = 0\big) \;\to\; u = 0.$$
--
--   In words: no nonzero vector is orthogonal (under $g_x$) to everything. This shows that the signature witness of the definition really carries the source's nondegeneracy, via the invertibility of the previous rung.
--
--   **Formalization note.** Testing argument: given `u` with all pairings zero, choose `v = (g x)^{-1} u` (exists by `hinv`); then $\mathrm{pair}(u, v) = \sum_{i,j} u_i\, g_{ij}\, (g^{-1} u)_j = u^{T} u = \|u\|^2 = 0$, forcing `u = 0` (Mathlib's squared-norm-implies-zero on Pi types, e.g. `Pi.norm_eq_zero` after `norm_eq_pow_two`-style rewriting, or componentwise via `sq_eq_zero_iff`). Neither symmetry nor smoothness is needed — the statement is pure finite-dimensional linear algebra.
-- source:
--   Wikipedia, Pseudo-Riemannian manifold, https://en.wikipedia.org/wiki/Pseudo-Riemannian_manifold (source of the quoted statements, reproduced verbatim in the definition file) ('That g is non-degenerate means there is no non-zero X in TpM such that g(X, Y) = 0 for all Y in TpM')

import Mathlib
import Definitions.Def_PseudoRiemannian

namespace PseudoRiemannian

open Matrix
open scoped ContDiff

/-- Milestone: the article's nondegeneracy, from invertibility.  "That g is
non-degenerate means there is no non-zero X in TpM such that g(X, Y) = 0 for
all Y in TpM."  If the metric matrix `g x` is invertible, then the pairing at
`x` is nondegenerate in exactly this sense: the only vector pairing to zero
with every other vector is the zero vector. -/
theorem nondegenerate_of_invertible {n : ℕ} {g : Spc n → Matrix (Fin n) (Fin n) ℝ}
    {x : Spc n} (hinv : IsUnit (g x).det) :
    IsNondegenerateAt g x := by
  sorry

end PseudoRiemannian
