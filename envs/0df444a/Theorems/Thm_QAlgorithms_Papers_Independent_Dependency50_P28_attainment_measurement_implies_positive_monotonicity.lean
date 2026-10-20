-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_attainment_measurement_implies_positive_monotonicity
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.attainment_measurement_implies_positive_monotonicity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T18:15:34.414856+00:00
-- url     : https://prove2.me/theorems/9a00410d-1b7d-46bd-942f-5de2886f7b5b
-- title:
--   AM and measurement monotonicity imply positive-map monotonicity
-- statement:
--   For a divergence family D over every finite dimension, suppose each state pair has an exactly attaining finite measurement (AM), and suppose D decreases under measurements (MMON). Then D decreases under every positive trace-preserving complex-linear map:
--
--   $$
--   \mathrm{AM}(D)+\mathrm{MMON}(D)\Longrightarrow\mathrm{PTPMON}(D).
--   $$
--
--   This turns exact measurement attainment into monotonicity under all positive trace-preserving maps.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 23, It is easy to see that

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P28

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (support positivePart positiveProjection)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- arXiv:1309.3228v5, PDF p.23: AM and measurement monotonicity imply positive-map monotonicity. AM is exact single-shot attainment, not AAM. The output’s attaining measurement is pulled back through the positive TP map; no complete positivity is imposed. -/
theorem attainment_measurement_implies_positive_monotonicity (d : Divergence) :
    AM d → MMON d → PTPMON d := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
