-- Prove2me | Theorems.Thm_PseudoRiemannian_sylvester_law_of_inertia
-- name    : PseudoRiemannian.sylvester_law_of_inertia
-- status  : Open
-- author  : @LG
-- created : 2026-11-27T02:30:47.507793+00:00
-- url     : https://prove2.me/theorems/597299eb-2167-5227-b612-46b1f5cbda30
-- title:
--   Sylvester's law of inertia: the signature is well defined (goal)
-- statement:
--   **Sylvester's law of inertia — the signature is well defined. The goal theorem.**
--
--   The source: "By Sylvester's law of inertia, the number of each positive, negative and zero values produced in this manner are invariants of the metric tensor, independent of the choice of orthogonal basis. The signature (p, q, r) of the metric tensor gives these numbers … A non-degenerate metric tensor has r = 0 and the signature may be denoted (p, q), where p + q = n."
--
--   Let $g(x)$ be a symmetric matrix, and suppose it is invertibly congruent to two signature diagonals:
--
--   $$B^{T}\, g(x)\, B = \mathrm{diag}(s), \qquad C^{T}\, g(x)\, C = \mathrm{diag}(s'),$$
--
--   with $B, C$ invertible and $s, s'$ taking values $\pm 1$.
--
--   **Conclusion:** the two diagonals have the same index:
--
--   $$\mathrm{negCount}(s) \;=\; \mathrm{negCount}(s')$$
--
--   (the number of entries equal to $-1$; by $p + q = n$ also the number of $+1$ entries agrees). In words: the signature of a nondegenerate symmetric bilinear form is an invariant of the form, not of the chosen orthogonal basis — exactly the invariance the article invokes. This is what makes "the signature (p, q) of a pseudo-Riemannian metric" a well-defined notion, and with it the whole signature-based classification of the source (Lorentzian, Riemannian, etc.).
--
--   **Formalization note.** A genuine classical theorem — Mathlib does not have Sylvester's law of inertia, so it must be proved. The standard dimension count: the $-1$-coordinates of `diag s` span a subspace $N$ of dimension `negCount s` on which the form is negative definite ($q(w, w) < 0$ for $w \neq 0$); the non-$-1$-coordinates of `diag s'` span a subspace $P$ of dimension $n - \mathrm{negCount}(s')$ on which the form is positive semidefinite ($q(w, w) \ge 0$). Pulled to the same space (through $B^{-1}$ and $C^{-1}$), $\dim N + \dim P = n + \mathrm{negCount}(s) - \mathrm{negCount}(s') > n$ if the counts differed, so $N \cap P$ contains a nonzero vector — but on it the form is simultaneously $< 0$ and $\ge 0$, a contradiction. Symmetry of $g(x)$ enters in the semidefiniteness direction (restricting a symmetric form to a subspace and pulling back along linear maps preserves symmetry); the argument then runs symmetrically to rule out `negCount s < negCount s'`. Harvest: `negCount` of a signature diagonal via `Finset.univ.filter`/cardinality lemmas; the subspace arguments via Mathlib's `Subspace`/dimension API.
-- source:
--   Wikipedia, Pseudo-Riemannian manifold, https://en.wikipedia.org/wiki/Pseudo-Riemannian_manifold (source of the quoted statements, reproduced verbatim in the definition file) ('By Sylvester's law of inertia, the number of each positive, negative and zero values produced in this manner are invariants of the metric tensor, independent of the choice of orthogonal basis. The signature (p, q, r) of the metric tensor gives these numbers'); J. J. Sylvester, law of inertia (1852); B. O'Neill, Semi-Riemannian Geometry With Applications to Relativity, Academic Press (1983)

import Mathlib
import Definitions.Def_PseudoRiemannian

namespace PseudoRiemannian

open Matrix
open scoped ContDiff

/-- The goal — Sylvester's law of inertia, the theorem the source invokes for
the signature: "By Sylvester's law of inertia, the number of each positive,
negative and zero values produced in this manner are invariants of the metric
tensor, independent of the choice of orthogonal basis. The signature (p, q, r)
of the metric tensor gives these numbers ... A non-degenerate metric tensor has
r = 0 and the signature may be denoted (p, q), where p + q = n."

In the diagonal normal form: if the symmetric matrix `g x` is invertibly
congruent to two signature diagonals, `Bᵀ (g x) B = diag s` and
`Cᵀ (g x) C = diag s'` with `s, s'` taking values `± 1`, then the two diagonals
have the same number of negative entries — `negCount s = negCount s'` — and
likewise the same number of positive entries.  The signature `(p, q)` of the
metric (here `(n - negCount s, negCount s)`) is therefore well defined: it does
not depend on the chosen orthogonal basis, only on the metric. -/
theorem sylvester_law_of_inertia {n : ℕ} {g : Spc n → Matrix (Fin n) (Fin n) ℝ}
    {x : Spc n} (hsymm : ∀ i j, g x i j = g x j i)
    {B C : Matrix (Fin n) (Fin n) ℝ} (hB : IsUnit B.det) (hC : IsUnit C.det)
    {s s' : Fin n → ℝ} (h1 : Bᵀ * g x * B = Matrix.diagonal s)
    (h2 : Cᵀ * g x * C = Matrix.diagonal s')
    (hs : IsSignVec s) (hs' : IsSignVec s') :
    negCount s = negCount s' := by
  sorry

end PseudoRiemannian
