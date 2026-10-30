-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P10_renyi_order_monotone
-- name    : QAlgorithms.Papers.Independent.Advance50.P10.renyi_order_monotone
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:32:41.414993+00:00
-- url     : https://prove2.me/theorems/f5afd590-5c5e-4dce-827e-75705894b7e3
-- title:
--   Lemma II.2: monotonicity in the order
-- statement:
--   All logarithms are base two. On a finite-dimensional complex Hilbert space $H$, write $S_\alpha(A\|B)$ for the paper’s unnormalized Petz Rényi relative entropy of positive semidefinite operators, with extended-real values, support-only powers, and the Umegaki value at order one. Let $A,B\ge0$ and $\operatorname{Tr}A\le1$. Then
--
--   $$\alpha\longmapsto S_\alpha(A\|B)\quad\text{is increasing on }[0,1)\text{ and separately on }(1,\infty).$$
--
--   If $\operatorname{Tr}A=1$, it is increasing on the entire interval $[0,\infty)$. Increasing means nondecreasing. There is no normalization restriction on $B$. The distinction between the two order intervals is essential for subnormalized numerators.
-- source:
--   On the quantum Renyi relative entropies and related capacity formulas, arXiv:0912.1286v4, PDF p. 4, Lemma II.2: monotonicity in the order

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

/-- Lemma II.2, PDF p.4: two separate monotonicity intervals for subnormalized A,
and the joined interval only for trace-one A. -/
theorem renyi_order_monotone {I : Type} [Fintype I] [DecidableEq I]
    (A B : Operator I) (hA : A.PosSemidef) (hB : B.PosSemidef) (htrace : A.trace.re ≤ 1) :
    MonotoneOn (fun a => petzRelativeBits a A B) (Ico 0 1) ∧
    MonotoneOn (fun a => petzRelativeBits a A B) (Ioi 1) ∧
    (A.trace.re = 1 → MonotoneOn (fun a => petzRelativeBits a A B) (Ici 0)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P10

end
