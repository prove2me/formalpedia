-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P10_renyi_entropy_bounds
-- name    : QAlgorithms.Papers.Independent.Advance50.P10.renyi_entropy_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:36:33.578001+00:00
-- url     : https://prove2.me/theorems/6730e32e-187f-4306-bb8a-7929e5c82fe5
-- title:
--   Unnumbered: entropy bounds (18)
-- statement:
--   All logarithms are base two. On a finite-dimensional complex Hilbert space $H$, write $S_\alpha(A\|B)$ for the paper’s unnormalized Petz Rényi relative entropy of positive semidefinite operators, with extended-real values, support-only powers, and the Umegaki value at order one. Let $\rho$ be a density operator, let $d=\dim H$, and define its Rényi entropy by $S_\alpha(\rho)=\log_2d-S_\alpha(\rho\|I/d)$. For every finite $\alpha\ge0$,
--
--   $$0\le S_\alpha(\rho)\le\log_2d.$$
--
--   The existence of $\rho$ ensures $d>0$. This bounds every finite-order entropy between the pure-state and uniform-state values.
-- source:
--   On the quantum Renyi relative entropies and related capacity formulas, arXiv:0912.1286v4, PDF p. 4, Unnumbered: entropy bounds (18)

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

/-- Entropy bounds (18), PDF p.4. A density cannot exist in dimension zero. -/
theorem renyi_entropy_bounds {I : Type} [Fintype I] [DecidableEq I]
    (rho : {A : Operator I // IsDensityMatrix A}) (a : ℝ) (ha : 0 ≤ a) :
    0 ≤ petzEntropyBits a rho.1 ∧ petzEntropyBits a rho.1 ≤ (Real.logb 2 (Fintype.card I : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P10

end
