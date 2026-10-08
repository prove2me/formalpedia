-- Prove2me | Theorems.Thm_SemialgebraicSDP_Psatz_theorem_3_3
-- name    : SemialgebraicSDP.Psatz.theorem_3_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:15:18.873976+00:00
-- url     : https://prove2.me/theorems/0441fd55-c015-4c8f-bae3-ed7112006204
-- title:
--   Theorem 3.3 — SOS of degree $2d$ is decided by an SDP of size $\binom{n+d}{d}$
-- statement:
--   Let $n,d\in\mathbb N$ and let $F\in\mathbb R[x_1,\dots,x_n]$ have total degree at most $2d$. Let $z$ be the vector of monomials of total degree at most $d$. Then
--   $$
--   F\text{ is a sum of squares}\iff\exists\,Q\succeq 0\ \text{ with }\ F=z^TQz,
--   $$
--   and the matrix $Q$ has size $\binom{n+d}{d}\times\binom{n+d}{d}$.
--
--   The right-hand side is a semidefinite feasibility problem: the set of matrices $Q$ with $F=z^TQz$ is an affine subspace (coefficient matching), intersected with the positive semidefinite cone. This is how the existence of a sum of squares decomposition is decided by semidefinite programming, and it is the step that turns the sum-of-squares multipliers of the Positivstellensatz into SDP variables.
--
--   **Formalization Note** The meta-claim "can be decided by solving a semidefinite programming feasibility problem" is rendered as the equivalence above with the explicit finite PSD system, together with the dimension count. "Degree $2d$" is read as total degree at most $2d$, the setting of (3.5). The clause "if the polynomial is dense (no sparsity)" only explains why the full monomial vector is used and adds no hypothesis.
-- source:
--   Parrilo, Semidefinite programming relaxations for semialgebraic problems, Math. Program. Ser. B 96 (2003) 293–320, p. 299, Theorem 3.3

import Mathlib
import Definitions.Def_SemialgebraicSDP_Psatz_Gram

namespace SemialgebraicSDP.Psatz

open MvPolynomial

theorem theorem_3_3 {n d : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (hdeg : F.totalDegree ≤ 2 * d) :
    (IsSumSq F ↔ ∃ Q : Matrix (Mon n d) (Mon n d) ℝ, Q.PosSemidef ∧ F = gramPoly Q) ∧
      Fintype.card (Mon n d) = (n + d).choose d := by sorry

end SemialgebraicSDP.Psatz
