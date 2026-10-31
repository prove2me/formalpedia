-- Prove2me | Theorems.Thm_SPQPoly_claim_3_2_2
-- name    : SPQPoly.claim_3_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:36:56.815973+00:00
-- url     : https://prove2.me/theorems/d2639ffe-ccbc-4726-a2c3-5188481e09f4
-- title:
--   Theorem 3.2, proof, claim (3.2.2) — the sextic $p$ is nonnegative at its critical points
-- statement:
--   Let $p$ be the polynomial of Theorem 3.2. For every $x\in\mathbb R^2$,
--   $$
--   \nabla p(x)=0\quad\Longrightarrow\quad p(x)\ge0 .
--   $$
--   Together with claim (3.2.1) this gives the nonnegativity of $p$.
--
--   Differences from the source:
--   - encoding: ∇p(x) = 0 → ∀ i, eval x (pderiv i p) = 0; reason: the formal partial derivatives of a polynomial are its partial derivatives
-- source:
--   Ahmadi, Dibek & Hall, Sums of Separable and Quadratic Polynomials, arXiv:2105.04766v1, Theorem 3.2, proof, claim (3.2.2), p.11

import Mathlib
import Definitions.Def_SPQPoly_p32

open MvPolynomial

namespace SPQPoly

/-- **Claim (3.2.2): the polynomial of Theorem 3.2 is nonnegative at its critical points.**
Ahmadi, Dibek & Hall, *Sums of Separable and Quadratic Polynomials*, arXiv:2105.04766v1, Theorem 3.2, proof, claim (3.2.2), p.11:
"(3.2.2) p(x) ≥ 0 for every x ∈ R2 that satisfies ∇p(x) = 0."

**Formalization Note.** `p` is `p32`, `ℝ²` is `Fin 2 → ℝ`, and `∇p(x) = 0` is
`∀ i, eval x (pderiv i p32) = 0`. -/
theorem claim_3_2_2 (x : Fin 2 → ℝ) (hx : ∀ i : Fin 2, eval x (pderiv i p32) = 0) :
    0 ≤ eval x p32 := by sorry

end SPQPoly
