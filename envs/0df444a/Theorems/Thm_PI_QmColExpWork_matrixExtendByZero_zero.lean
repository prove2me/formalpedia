-- Prove2me | Theorems.Thm_PI_QmColExpWork_matrixExtendByZero_zero
-- name    : PI.QmColExpWork.matrixExtendByZero_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:16:47.20457+00:00
-- url     : https://prove2.me/theorems/c2c67317-23d1-4554-8adc-ee15a99b1b63
-- title:
--   Qm Col Exp Work: matrix Extend By Zero zero
-- statement:
--   The Qm Col Exp Work construction uses the matrix Extend By Zero zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialFirstColumn/FirstColumnSplitBijective.lean#L34-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialFirstColumn/FirstColumnSplitBijective.lean#L34-L35

import Definitions.Def_Formalism_PeriodIntegrals_QmColExp
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialFirstColumn_FirstColumnSplitBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open PI PI.QmColExpWork
open Formalism.REAL

theorem PI.QmColExpWork.matrixExtendByZero_zero {m : ℕ} (τ : Equiv.Perm (Fin m)) : ext0 τ 0 = 0 := by sorry
