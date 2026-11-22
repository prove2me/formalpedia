-- Prove2me | Theorems.Thm_PI_QmColExpWork_cycle_perm_zero
-- name    : PI.QmColExpWork.cycle_perm_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:16:20.225252+00:00
-- url     : https://prove2.me/theorems/5ff35f83-3354-4c35-9333-653a5596c0a4
-- title:
--   Qm Col Exp Work: cycle perm zero
-- statement:
--   The Qm Col Exp Work construction uses the cycle perm zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialFirstColumn/FirstColumnSplitBijective.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialFirstColumn/FirstColumnSplitBijective.lean#L14-L18

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

theorem PI.QmColExpWork.cycle_perm_zero (m : ℕ) (j : Fin (m + 1)) : cyc0 m j 0 = j := by sorry
