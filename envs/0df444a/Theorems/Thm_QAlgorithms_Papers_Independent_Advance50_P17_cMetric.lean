-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P17_cMetric
-- name    : QAlgorithms.Papers.Independent.Advance50.P17.cMetric
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:22:49.56268+00:00
-- url     : https://prove2.me/theorems/6b0449fa-1b69-4504-9603-0aa6fe765c1f
-- title:
--   Section III: C is a metric on normalized states
-- statement:
--   On normalized density matrices of every positive finite dimension, let $F(\rho,\sigma)=[\operatorname{tr}\sqrt{\sqrt\rho\,\sigma\sqrt\rho}]^2$ and $C(\rho,\sigma)=\sqrt{1-F(\rho,\sigma)}$. Then $C$ is nonnegative and symmetric, vanishes exactly when its arguments coincide, and satisfies
--
--   $$C(\rho,\tau)\le C(\rho,\sigma)+C(\sigma,\tau).$$
--
--   This supplies a fidelity-derived state metric; pure vectors enter through their density matrices, so global phase is immaterial.
-- source:
--   Distance measures to compare real and ideal quantum processes, arXiv:quant-ph/0408063v2, PDF p. 4, Section III: C is a metric on normalized states

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P17

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate Topology

namespace QAlgorithms.Papers.Independent.Advance50.P17

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P75 (hermitianReal)

variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]
  [Nonempty I] [Nonempty J] [Nonempty K]

/-- Section III, PDF p.4 (proof note [38], p.15): C is a metric on normalized density matrices.
The overstrong simultaneous-purification assertion in note [38] is not a hypothesis. -/
theorem cMetric : MetricAxioms (fun rho sigma : ProcessDensityInput I => stateDistance .sine rho.val sigma.val) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P17

end
