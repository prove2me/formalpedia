-- Prove2me | Theorems.Thm_PI_QmRowExpWork_firstColumnSplit_bijective
-- name    : PI.QmRowExpWork.firstColumnSplit_bijective
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:17:31.921858+00:00
-- url     : https://prove2.me/theorems/04ecfdc1-1634-474e-aeb4-aad45d7cae7e
-- title:
--   Qm Row Exp Work: first Column Split bijective
-- statement:
--   The Qm Row Exp Work construction uses the first Column Split bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RowExpansionMinor/FirstColumnSplitBijective.lean#L43-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RowExpansionMinor/FirstColumnSplitBijective.lean#L43-L59

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

theorem PI.QmRowExpWork.firstColumnSplit_bijective (m : ℕ) : Function.Bijective (phi0 m) := by sorry
