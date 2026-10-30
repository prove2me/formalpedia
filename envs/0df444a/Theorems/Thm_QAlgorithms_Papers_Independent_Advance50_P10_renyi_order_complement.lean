-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P10_renyi_order_complement
-- name    : QAlgorithms.Papers.Independent.Advance50.P10.renyi_order_complement
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:35:40.644631+00:00
-- url     : https://prove2.me/theorems/266da331-bb48-47ba-b270-23dc2f4aec4c
-- title:
--   Unnumbered: order-complement symmetry (11)
-- statement:
--   All logarithms are base two. On a finite-dimensional complex Hilbert space $H$, write $S_\alpha(A\|B)$ for the paper’s unnormalized Petz Rényi relative entropy of positive semidefinite operators, with extended-real values, support-only powers, and the Umegaki value at order one. For arbitrary $A,B\ge0$ and $0<\alpha<1$,
--
--   $$S_{1-\alpha}(A\|B)=\frac{1-\alpha}{\alpha}S_\alpha(B\|A).$$
--
--   The identity includes zero and nonnormalized arguments and infinite divergence values. It relates the two complementary orders without a trace normalization.
-- source:
--   On the quantum Renyi relative entropies and related capacity formulas, arXiv:0912.1286v4, PDF p. 3, Unnumbered: order-complement symmetry (11)

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

/-- Order-complement symmetry (11), PDF p.3, for unrestricted PSD arguments. -/
theorem renyi_order_complement {I : Type} [Fintype I] [DecidableEq I]
    (A B : Operator I) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (a : ℝ) (ha : 0 < a) (ha_one : a < 1) :
    petzRelativeBits (1 - a) A B = (((1 - a) / a : ℝ) : EReal) * petzRelativeBits a B A := by sorry

end QAlgorithms.Papers.Independent.Advance50.P10

end
