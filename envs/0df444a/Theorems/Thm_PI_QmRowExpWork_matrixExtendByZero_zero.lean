-- Prove2me | Theorems.Thm_PI_QmRowExpWork_matrixExtendByZero_zero
-- name    : PI.QmRowExpWork.matrixExtendByZero_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:38:49.212854+00:00
-- url     : https://prove2.me/theorems/a3addc19-3357-48a5-9372-8346580c5074
-- title:
--   Qm Row Exp Work: matrix Extend By Zero zero
-- statement:
--   The Qm Row Exp Work construction uses the matrix Extend By Zero zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RowExpansionMinor/FirstColumnSplitBijective.lean#L30-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RowExpansionMinor/FirstColumnSplitBijective.lean#L30-L31

import Definitions.Def_Formalism_PeriodIntegrals_QmRowExp
import Definitions.Def_Formalism_PeriodIntegrals_QmRowForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowExpansionMinor_FirstColumnSplitBijective
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
open PI PI.QmRowExpWork
open Formalism.REAL

theorem PI.QmRowExpWork.matrixExtendByZero_zero {m : ℕ} (τ : Equiv.Perm (Fin m)) : ext0 τ 0 = 0 := by sorry
