-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P10_direct_order_cutoff
-- name    : QAlgorithms.Papers.Independent.Advance50.P10.direct_order_cutoff
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:39:15.683731+00:00
-- url     : https://prove2.me/theorems/162fba31-1336-4da9-a5e3-17d3a114d853
-- title:
--   Corollary III.2: direct order parameterization
-- statement:
--   All logarithms are base two. On a finite-dimensional complex Hilbert space $H$, write $S_\alpha(A\|B)$ for the paper’s unnormalized Petz Rényi relative entropy of positive semidefinite operators, with extended-real values, support-only powers, and the Umegaki value at order one. For density operators $\rho,\sigma$ and $0<\alpha<1$, let $C_\kappa$ denote the operational negative-slope cutoff defined from binary effects, strict first-kind limsup error constraints, and the upper second-kind exponent; the zero-constraint endpoint uses its right limit. Then
--
--   $$S_\alpha(\rho\|\sigma)=\frac\alpha{1-\alpha}C_{\alpha/(\alpha-1)}(\rho\|\sigma)=C_{(\alpha-1)/\alpha}(\sigma\|\rho).$$
--
--   Both cutoff slopes are negative. This is the direct order parameterization of the operational interpretation.
-- source:
--   On the quantum Renyi relative entropies and related capacity formulas, arXiv:0912.1286v4, PDF p. 5, Corollary III.2: direct order parameterization

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

/-- Corollary III.2, PDF p.5. Both cutoff subscripts are negative. -/
theorem direct_order_cutoff {I : Type} [Fintype I] [DecidableEq I]
    (rho sigma : {A : Operator I // IsDensityMatrix A}) (a : ℝ) (ha : 0 < a) (ha_one : a < 1) :
    petzRelativeBits a rho.1 sigma.1 = ((a / (1 - a) : ℝ) : EReal) *
      testingCutoff (fun n => n) (fun n => copies n rho.1) (fun n => copies n sigma.1) (a / (a - 1)) ∧
    petzRelativeBits a rho.1 sigma.1 =
      testingCutoff (fun n => n) (fun n => copies n sigma.1) (fun n => copies n rho.1) ((a - 1) / a) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P10

end
