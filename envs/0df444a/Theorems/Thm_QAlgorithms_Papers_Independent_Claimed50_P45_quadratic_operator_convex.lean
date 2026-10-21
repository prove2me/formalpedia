-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P45_quadratic_operator_convex
-- name    : QAlgorithms.Papers.Independent.Claimed50.P45.quadratic_operator_convex
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:15:28.717209+00:00
-- url     : https://prove2.me/theorems/8d4c1aa0-ca0d-4f00-8204-38936f93a38e
-- title:
--   Loewner convexity of the quadratic operator map
-- statement:
--   Let $\mathcal H$ be a finite-dimensional complex Hilbert space, let $A$ be a positive semidefinite operator on $\mathcal H$, and define $f_A(X)=X^*AX$ for every linear operator $X$. For all linear operators $X,Y$ and every real $t\in[0,1]$,
--
--   $$
--   f_A(tX+(1-t)Y)\preceq t f_A(X)+(1-t)f_A(Y).
--   $$
--
--   Here $X^*$ is the adjoint, and $B\preceq C$ means that $C-B$ is positive semidefinite. The operators $X$ and $Y$ need not be Hermitian, and $A$ need not have trace one.
--
--   This is convexity of the quadratic map on the real vector space of all complex operators, as used in the source's pinching inequality argument.
-- source:
--   On Error Exponents in Quantum Hypothesis Testing, arXiv:quant-ph/0206151v3, PDF p. 11, Lemma 5, equations (62)–(63)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P45

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P45

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

open Filter Topology QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (positiveProjection)

open QAlgorithms.Papers.Independent.Dependency50.P28
  (LE pinch logNonnegativeExtended typeI accept scaled TestSequence)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I : Type} [Fintype I] [DecidableEq I]

/-- PDF p.11, Lemma 5, (62)–(63): Loewner convexity of X ↦ X* A X on
ALL complex matrices, with a positive semidefinite A and real t in [0,1].
Neither normalization of A nor Hermiticity of X or Y is assumed. -/
theorem quadratic_operator_convex
    (A : Mat I) (hA : A.PosSemidef) (X Y : Mat I)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    LE (((t : ℂ) • X + ((1 - t : ℝ) : ℂ) • Y)ᴴ * A *
          ((t : ℂ) • X + ((1 - t : ℝ) : ℂ) • Y))
      ((t : ℂ) • (Xᴴ * A * X) + ((1 - t : ℝ) : ℂ) • (Yᴴ * A * Y)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P45

end
