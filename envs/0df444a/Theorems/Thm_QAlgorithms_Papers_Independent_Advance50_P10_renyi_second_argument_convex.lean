-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P10_renyi_second_argument_convex
-- name    : QAlgorithms.Papers.Independent.Advance50.P10.renyi_second_argument_convex
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:31:42.333299+00:00
-- url     : https://prove2.me/theorems/48c021f7-079d-4e5b-ad06-3cf91b2a38ff
-- title:
--   Theorem II.1: convexity in the second argument
-- statement:
--   All logarithms are base two. On a finite-dimensional complex Hilbert space $H$, write $S_\alpha(A\|B)$ for the paper’s unnormalized Petz Rényi relative entropy of positive semidefinite operators, with extended-real values, support-only powers, and the Umegaki value at order one. For any fixed positive semidefinite $A$, any positive semidefinite $B,C$, any $0\le\alpha\le2$, and any $0<t<1$,
--
--   $$S_\alpha(A\|(1-t)B+tC)\le(1-t)S_\alpha(A\|B)+tS_\alpha(A\|C).$$
--
--   No nonzero or unit-trace condition is imposed on $A$. This is convexity in the second argument, including singular operators.
-- source:
--   On the quantum Renyi relative entropies and related capacity formulas, arXiv:0912.1286v4, PDF p. 3, Theorem II.1: convexity in the second argument

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P10

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate ENNReal Topology

open Filter Set MeasureTheory

namespace QAlgorithms.Papers.Independent.Advance50.P10

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P58 (Operator)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart)

open QAlgorithms.Papers.Independent.Dependency50.P18 (logBits)

open QAlgorithms.Papers.Independent.Dependency50.P25 (extendedIntegral)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Bridge50.P45 (tensorEntries lifted comparison)

-- Density subtypes below reuse the frozen PSD/trace-one predicate directly.

-- The source uses Borel laws, with the weak topology on probability measures.

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P10.densityMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P10.densityBorelSpace

/-- Theorem II.1, PDF pp.3–4: convexity for every PSD numerator, including zero.
Interior weights avoid undefined endpoint products with infinite values. -/
theorem renyi_second_argument_convex {I : Type} [Fintype I] [DecidableEq I]
    (A B C : Operator I) (hA : A.PosSemidef) (hB : B.PosSemidef) (hC : C.PosSemidef)
    (a : ℝ) (ha : 0 ≤ a) (ha_two : a ≤ 2) (t : ℝ) (ht : 0 < t) (ht_one : t < 1) :
    petzRelativeBits a A (AffineMap.lineMap B C t) ≤
      ((1 - t : ℝ) : EReal) * petzRelativeBits a A B + (t : EReal) * petzRelativeBits a A C := by sorry

end QAlgorithms.Papers.Independent.Advance50.P10

end
