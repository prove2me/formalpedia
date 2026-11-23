-- Prove2me | Theorems.Thm_PI_QmRowExpWork_extByZero_succ
-- name    : PI.QmRowExpWork.extByZero_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:39:00.266068+00:00
-- url     : https://prove2.me/theorems/abe3ae75-1351-4b83-b294-12d19b26607c
-- title:
--   Qm Row Exp Work: ext By Zero succ
-- statement:
--   The Qm Row Exp Work construction uses the ext By Zero succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RowExpansionMinor/FirstColumnSplitBijective.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RowExpansionMinor/FirstColumnSplitBijective.lean#L33-L34

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

theorem PI.QmRowExpWork.extByZero_succ {m : ℕ} (τ : Equiv.Perm (Fin m)) (k : Fin m) : ext0 τ k.succ = (τ k).succ := by sorry
