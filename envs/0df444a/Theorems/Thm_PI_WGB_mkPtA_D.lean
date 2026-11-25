-- Prove2me | Theorems.Thm_PI_WGB_mkPtA_D
-- name    : PI.WGB.mkPtA_D
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:48:06.549022+00:00
-- url     : https://prove2.me/theorems/bf94af14-774b-40f4-a639-85a781e62a59
-- title:
--   WGB: mk Pt A D
-- statement:
--   The WGB construction uses the mk Pt A D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/ProdMkPtA.lean#L134-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/ProdMkPtA.lean#L134-L143

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_CoeffRowActDiagA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_StepACleared
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ProdMkPtA
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
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
variable {n : ℕ}

theorem PI.WGB.mkPtA_D (dv : Fin n → ℂ) (z : Fin (n + 1) → ℂ) : IsDPtA (mkPtA dv z) := by sorry
