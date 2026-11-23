-- Prove2me | Theorems.Thm_PI_QmColExpWork_firstColumnSplit_bijective
-- name    : PI.QmColExpWork.firstColumnSplit_bijective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:38:31.052975+00:00
-- url     : https://prove2.me/theorems/a6c48629-9262-4613-9f8d-b4f78fce75a6
-- title:
--   Qm Col Exp Work: first Column Split bijective
-- statement:
--   The Qm Col Exp Work construction uses the first Column Split bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialFirstColumn/FirstColumnSplitBijective.lean#L50-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialFirstColumn/FirstColumnSplitBijective.lean#L50-L65

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

theorem PI.QmColExpWork.firstColumnSplit_bijective (m : ℕ) : Function.Bijective (phi0 m) := by sorry
