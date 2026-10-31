-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P12_delayed_choi_characterization
-- name    : QAlgorithms.Papers.Independent.Intake100.P12.delayed_choi_characterization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:04:23.984633+00:00
-- url     : https://prove2.me/theorems/11a8e149-e5e7-4405-8141-77b937bbdc23
-- title:
--   Delayed parallel Choi normalization and realization
-- statement:
--   Let every external and slot wire have positive finite dimension, and write $I=\bigotimes_i I_i$ and $O=\bigotimes_i O_i$. In wire order $I_0,I,O,O_0$, a matrix $C_D$ is the Choi matrix of a parallel delayed-input protocol if and only if
--
--   $$C_D\succeq0,\qquad \operatorname{Tr}_{O_0}C_D=\frac{I_{I_0}}{d_{I_0}}\otimes\operatorname{Tr}_{I_0OO_0}C_D\otimes\frac{I_O}{d_O},\qquad\operatorname{Tr}C_D=d_{I_0}d_O.$$
--
--   Realization means preparing a fixed normalized state on oracle inputs and memory before the external input exists, using one parallel oracle batch, and applying a fixed CPTP decoder to that program and the later input. All tensor placements are as displayed.
--
--   This characterization includes physical realization in both directions; it introduces no delayed-input indefinite-order class.
-- source:
--   Probabilistic exact universal quantum circuits for transforming unitary operations, arXiv:1909.01366v2, PDF p. 9, IV, Eqs. (32)–(35)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P12

noncomputable section

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Kronecker

namespace QAlgorithms.Papers.Independent.Intake100.P12

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Dependency50.P26 (ChannelChoi)

/-- PDF p.9, Eqs. (32)–(35): complete delayed parallel Choi characterization,
including existence of a normalized resource and a CPTP decoder. -/
theorem delayed_choi_characterization {k : ℕ} (w : OracleWireDimensions k)
    (hw : PositiveWires w) (C : Op (ProcessBasis w)) :
    (C.PosSemidef ∧ DelayedRealizes w C) ↔ DelayedNormalized w C := by sorry

end QAlgorithms.Papers.Independent.Intake100.P12

end
