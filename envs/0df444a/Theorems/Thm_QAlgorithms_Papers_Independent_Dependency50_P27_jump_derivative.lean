-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P27_jump_derivative
-- name    : QAlgorithms.Papers.Independent.Dependency50.P27.jump_derivative
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:54:11.899977+00:00
-- url     : https://prove2.me/theorems/57c72513-ba16-4604-bafd-4ed9eef42173
-- title:
--   §5.3.2, unnumbered jump at a root
-- statement:
--   Let $R$ be a discrete ordered field equipped with a witness-returning intermediate value operation for polynomials. No completeness or Archimedean hypothesis is imposed. For $P\ne0$, a root $x$ of $P$, and arbitrary $Q$, let $\operatorname{jump}_x(A/B)$ be $+1$ for a crossing from negative infinity on the left to positive infinity on the right, $-1$ for the reverse crossing, and zero otherwise. Then
--
--   $$\operatorname{jump}_x\!\left(\frac{QP'}P\right)=\operatorname{sgn}(Q(x)).$$
--
--   Multiple roots are allowed; the jump definition uses multiplicities and right signs.
-- source:
--   Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination, arXiv:1201.3731v2, PDF p. 25, §5.3.2, unnumbered jump at a root

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

namespace QAlgorithms.Papers.Independent.Dependency50.P27

noncomputable section

open Polynomial

/-- Source PDF p. 25, jump of Q*P'/P at a root of a nonzero P. -/
theorem jump_derivative {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (p q : Polynomial R) (x : R)
    (hp : p ≠ 0) (hx : p.eval x = 0) :
    cauchyJump (q * p.derivative) p x = sgr (q.eval x) := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P27
