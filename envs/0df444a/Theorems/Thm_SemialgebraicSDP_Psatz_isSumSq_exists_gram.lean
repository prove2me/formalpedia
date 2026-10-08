-- Prove2me | Theorems.Thm_SemialgebraicSDP_Psatz_isSumSq_exists_gram
-- name    : SemialgebraicSDP.Psatz.isSumSq_exists_gram
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:15:18.061015+00:00
-- url     : https://prove2.me/theorems/a8e11e16-a3e7-4971-be42-a11d034a4fad
-- title:
--   §3.2 — a sum of squares of degree $\le 2d$ has a positive semidefinite Gram matrix
-- statement:
--   Let $n,d\in\mathbb N$ and let $F\in\mathbb R[x_1,\dots,x_n]$ be a sum of squares of polynomials with total degree at most $2d$. Then there is a real positive semidefinite matrix $Q$, indexed by the monomials of total degree at most $d$, such that
--   $$
--   F=z^TQz,
--   $$
--   where $z$ is the vector of these monomials.
--
--   This is the necessity half of the Gram matrix method. Its content includes the fact that in a representation $F=\sum_i p_i^2$ every $p_i$ already has degree at most $d$, because the leading forms of real squares cannot cancel; it is not assumed.
-- source:
--   Parrilo, Semidefinite programming relaxations for semialgebraic problems, Math. Program. Ser. B 96 (2003) 293–320, pp. 298–299, §3.2

import Mathlib
import Definitions.Def_SemialgebraicSDP_Psatz_Gram

namespace SemialgebraicSDP.Psatz

open MvPolynomial

theorem isSumSq_exists_gram {n d : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (hF : IsSumSq F) (hdeg : F.totalDegree ≤ 2 * d) :
    ∃ Q : Matrix (Mon n d) (Mon n d) ℝ, Q.PosSemidef ∧ F = gramPoly Q := by sorry

end SemialgebraicSDP.Psatz
