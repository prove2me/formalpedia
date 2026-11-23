-- Prove2me | Theorems.Thm_PI_QmRowExpWork_cycle_perm_zero
-- name    : PI.QmRowExpWork.cycle_perm_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:38:45.043885+00:00
-- url     : https://prove2.me/theorems/fab78164-c3ec-4b04-817f-9868b949b5a2
-- title:
--   Qm Row Exp Work: cycle perm zero
-- statement:
--   The Qm Row Exp Work construction uses the cycle perm zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RowExpansionMinor/FirstColumnSplitBijective.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RowExpansionMinor/FirstColumnSplitBijective.lean#L15-L17

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

theorem PI.QmRowExpWork.cycle_perm_zero (m : ℕ) (j : Fin (m + 1)) : cyc0 m j 0 = j := by sorry
