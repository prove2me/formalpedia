-- Prove2me | Theorems.Thm_PI_QmRowExpWork_expFirstRow_of
-- name    : PI.QmRowExpWork.expFirstRow_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:38:50.441508+00:00
-- url     : https://prove2.me/theorems/48dbf87f-8b87-4680-ab32-fa135686fa16
-- title:
--   Qm Row Exp Work: exp First Row of
-- statement:
--   The Qm Row Exp Work construction uses the exp First Row of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RowExpansionMinor/FirstColumnSplitBijective.lean#L112-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RowExpansionMinor/FirstColumnSplitBijective.lean#L112-L116

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

theorem PI.QmRowExpWork.expFirstRow_of (h : PI.RowForm) : PI.ExpFirstRow := by sorry
