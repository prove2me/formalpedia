-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P46_trace_decrease_counterexample
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P46.trace_decrease_counterexample
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:29:27.003174+00:00
-- url     : https://prove2.me/theorems/e6a949af-250b-4501-a7bb-ae98e2d814fc
-- title:
--   A completely positive trace-decreasing map can increase relative entropy
-- statement:
--   On complex $2\times2$ matrices define $\Phi\left(\begin{smallmatrix}v&w\\x&y\end{smallmatrix}\right)=\operatorname{diag}(v/2,y)$ and fix the density matrices $\rho=\operatorname{diag}(1/3,2/3)$ and $\sigma=\operatorname{diag}(2/3,1/3)$. The map is complex-linear, completely positive, and trace-nonincreasing on every positive matrix. Nevertheless, for literal unnormalized relative entropy in natural units,
--
--   $$D(\rho\Vert\sigma)=\frac{\log2}{3}<\frac{\log2}{2}=D(\Phi(\rho)\Vert\Phi(\sigma)).$$
--
--   The output operators have traces $5/6$ and $2/3$ and are not asserted to be normalized. This counterexample explains why trace nonincrease alone does not suffice for the Umegaki data-processing inequality.
-- source:
--   Monotonicity of the Quantum Relative Entropy Under Positive Maps, arXiv:1512.06117v3, PDF p. 3, Unnumbered counterexample: trace nonincrease alone does not give relative-entropy monotonicity

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P46

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Intakethird100.P46

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsTraceClass TraceClass IsPositive operatorTrace)

open QAlgorithms.Papers.Independent.Dependency50.P35 (Dominates)

open QAlgorithms.Papers.Independent.Bridge50.P49 (beigiSandwichedDivergence)

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Müller-Hermes–Reeb, arXiv:1512.06117v3, PDF p.3, unnumbered counterexample.
Both INPUTS are density matrices. The CP trace-nonincreasing map produces
subnormalized operators, and the two literal relative entropies increase strictly. -/
theorem trace_decrease_counterexample :
    Entanglement.IsCompletelyPositive traceDecreaseMap ∧
    PositiveMatrixTraceNonincreasing traceDecreaseMap ∧
    IsDensityMatrix counterexampleRho ∧ IsDensityMatrix counterexampleSigma ∧
    finiteLiteralRelativeEntropy counterexampleRho counterexampleSigma =
      ((Real.log 2 / 3 : ℝ) : EReal) ∧
    ((Real.log 2 / 3 : ℝ) : EReal) < ((Real.log 2 / 2 : ℝ) : EReal) ∧
    finiteLiteralRelativeEntropy (traceDecreaseMap counterexampleRho)
      (traceDecreaseMap counterexampleSigma) = ((Real.log 2 / 2 : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P46

end
