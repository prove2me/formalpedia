-- Prove2me | Theorems.Thm_PI_QmRowExpWork_sign_extend_perm
-- name    : PI.QmRowExpWork.sign_extend_perm
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:17:40.088719+00:00
-- url     : https://prove2.me/theorems/561e20d3-e738-5e17-81a7-d21f1f55923b
-- title:
--   Qm Row Exp Work: sign extend perm
-- statement:
--   The Qm Row Exp Work construction uses the sign extend perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RowExpansionMinor/FirstColumnSplitBijective.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RowExpansionMinor/FirstColumnSplitBijective.lean#L36-L38

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

theorem PI.QmRowExpWork.sign_extend_perm {m : ℕ} (τ : Equiv.Perm (Fin m)) :
    Equiv.Perm.sign (ext0 τ) = Equiv.Perm.sign τ := by sorry
