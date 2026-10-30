-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P15_qubit_covariant_error_calibration
-- name    : QAlgorithms.Papers.Independent.Extend50.P15.qubit_covariant_error_calibration
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:00:41.183356+00:00
-- url     : https://prove2.me/theorems/3b231716-f06d-43b3-8aa9-bed414d030ed
-- title:
--   Exact worst-case error calibration for an SU(2)-covariant qubit channel
-- statement:
--   Let $\mathcal A$ be a CPTP qubit channel that commutes with conjugation by every $U\in\mathrm{SU}(2)$. Let $F_{\mathrm{ent}}(\mathcal A,\mathcal I)$ denote squared Uhlmann fidelity between the normalized Choi states of $\mathcal A$ and identity. Then
--
--   $$\frac12\|\mathcal A-\mathcal I\|_\diamond=1-F_{\mathrm{ent}}(\mathcal A,\mathcal I).$$
--
--   The left side includes arbitrary entangled references. This calibrates the entire covariant effective qubit channel; an arbitrary noncovariant channel does not satisfy the asserted equality.
-- source:
--   Optimal Universal Quantum Error Correction via Bounded Reference Frames, arXiv:2007.09154v2, PDF p. 31, Appendix E, final paragraph

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P15

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P15

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P75 (Register)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Appendix E, final paragraph, PDF p.31: analytical calibration of the entire
SU(2)-covariant effective channel. This is not a theorem about noncovariant simulation noise. -/
theorem qubit_covariant_error_calibration (A : Superop (Fin 2) (Fin 2))
    (hA : IsChannel A) (hcov : IsSUChannelCovariant A) :
    stabilizedHalfDiamondError A id = 1 - choiPairFidelity 2 (by norm_num) A id := by sorry

end QAlgorithms.Papers.Independent.Extend50.P15

end
