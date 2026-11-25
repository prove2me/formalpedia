-- Prove2me | Theorems.Thm_PI_WGB_chiB_smul
-- name    : PI.WGB.chiB_smul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:45:45.325164+00:00
-- url     : https://prove2.me/theorems/80f2d6a4-0b43-4a53-9969-c78df33cdd28
-- title:
--   WGB: chi B smul
-- statement:
--   The WGB construction uses the chi B smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/RowActDiagMonomial.lean#L41-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/RowActDiagMonomial.lean#L41-L42

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFEqSumOfSubsetB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RowActDiagMonomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions MvPolynomial

theorem PI.WGB.chiB_smul {n : ℕ} (t : Fin n → ℂ) (k : ℕ) (a : Fin n → ℕ) : chiB t (k • a) = chiB t a ^ k := by sorry
