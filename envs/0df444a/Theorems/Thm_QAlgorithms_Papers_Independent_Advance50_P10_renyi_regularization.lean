-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P10_renyi_regularization
-- name    : QAlgorithms.Papers.Independent.Advance50.P10.renyi_regularization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:34:45.846137+00:00
-- url     : https://prove2.me/theorems/e892876f-17c8-4a58-ba91-e69540ba8f58
-- title:
--   Unnumbered: regularization identities (12)–(13)
-- statement:
--   All logarithms are base two. On a finite-dimensional complex Hilbert space $H$, write $S_\alpha(A\|B)$ for the paper’s unnormalized Petz Rényi relative entropy of positive semidefinite operators, with extended-real values, support-only powers, and the Umegaki value at order one. For arbitrary $A,B\ge0$ and $\alpha\ge0$,
--
--   $$S_\alpha(A\|B)=\sup_{\varepsilon>0}S_\alpha(A\|B+\varepsilon I).$$
--
--   For $\alpha
--   e1$ the signed quasi-relative entropy $Q_\alpha$ obeys the same formula:
--
--   $$Q_\alpha(A\|B)=\sup_{\varepsilon>0}Q_\alpha(A\|B+\varepsilon I).$$
--
--   The suprema lie in the extended real line. These identities extend the strictly positive second-argument formulas to singular operators; $Q_1$ is not a source-defined quantity.
-- source:
--   On the quantum Renyi relative entropies and related capacity formulas, arXiv:0912.1286v4, PDF p. 3, Unnumbered: regularization identities (12)–(13)

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

/-- Regularization identities (12)–(13), PDF p.3. Q is defined only away from one;
S includes its separately defined order-one value. -/
theorem renyi_regularization {I : Type} [Fintype I] [DecidableEq I]
    (A B : Operator I) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (a : ℝ) (ha : 0 ≤ a) :
    petzRelativeBits a A B = (⨆ e : {e : ℝ // 0 < e}, petzRelativeBits a A (perturb B e.1)) ∧
    (a ≠ 1 → quasiRelative a A B =
      ⨆ e : {e : ℝ // 0 < e}, quasiRelative a A (perturb B e.1)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P10

end
