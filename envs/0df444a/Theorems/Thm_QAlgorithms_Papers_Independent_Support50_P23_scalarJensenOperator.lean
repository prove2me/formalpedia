-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P23_scalarJensenOperator
-- name    : QAlgorithms.Papers.Independent.Support50.P23.scalarJensenOperator
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T21:04:03.510857+00:00
-- url     : https://prove2.me/theorems/d9ed768d-cf8d-474d-84fd-f59ee74b6fc4
-- title:
--   Scalar Jensen inequality applied to an operator
-- statement:
--   Let $a\le b$ be real, let $f:\mathbb R\to\mathbb R$ be convex on $[a,b]$, let $X$ be Hermitian on a finite-dimensional nonzero complex Hilbert space with $aI\preceq X\preceq bI$, and let $\|\phi\|=1$. Functional calculus gives
--   $$
--   f(\langle\phi|X|\phi\rangle)\le\langle\phi|f(X)|\phi\rangle.
--   $$
--   Both matrix elements are real. The unit-norm condition repairs the printed preamble, which omits it, and matches the normalized-purification applications on pages 5 and 8. The uncorrected statement fails for $f=1$, $X=0$, $\phi=0$. This is the scalar convexity tool used in the entropy estimates.
-- source:
--   A Fully Quantum Asymptotic Equipartition Property, arXiv:0811.1221v3, PDF p. 6, Lemma 11: scalar Jensen applied to an operator

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P23

noncomputable section

open Filter

open scoped ENNReal ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Support50.P23

attribute [local instance] Classical.propDecidable

-- Exact accepted bodies. Other similarly named catalogue entries use different
-- smoothing, conditioning order, logarithm base, or channel-level objects.

open QAlgorithms.Papers.Independent.Gap20.P03 (fixedMin)

open QAlgorithms.Papers.Independent.Dependency50.P36 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)

open QAlgorithms.Papers.Independent.Information100.P69 (matrixPower)

variable {A B C D I : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype I]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D] [DecidableEq I]

/-- Lemma 11, PDF p.6. Printed/changed/why: add norm-one phi, as used for the
normalized purifications on pp.5,8. The literal preamble allows f=1,X=0,phi=0,
which gives 0>=1. Hermiticity is implicit in the source's Loewner comparisons. -/
theorem scalarJensenOperator [Nonempty I]
    (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Icc a b) f)
    (X : Matrix I I ℂ) (hX : X.IsHermitian)
    (hLower : (X - (a : ℂ) • (1 : Matrix I I ℂ)).PosSemidef)
    (hUpper : ((b : ℂ) • (1 : Matrix I I ℂ) - X).PosSemidef)
    (phi : EuclideanSpace ℂ I) (hphi : ‖phi‖ = 1) :
    f ((inner ℂ phi (act X phi)).re) ≤ (inner ℂ phi (act (cfc f X) phi)).re := by sorry

end QAlgorithms.Papers.Independent.Support50.P23

end
