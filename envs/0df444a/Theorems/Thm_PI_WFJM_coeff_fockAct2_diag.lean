-- Prove2me | Theorems.Thm_PI_WFJM_coeff_fockAct2_diag
-- name    : PI.WFJM.coeff_fockAct2_diag
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:44:07.878737+00:00
-- url     : https://prove2.me/theorems/9c34fcf6-bfd6-478e-98ef-0306a2e339e2
-- title:
--   WFJM: coeff fock Act2 diag
-- statement:
--   The WFJM construction uses the coeff fock Act2 diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L610-L619
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L610-L619

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.WFJM
open MvPolynomial
open PI.FJM
variable {p q r s : ℕ}
open MvPolynomial

theorem PI.WFJM.coeff_fockAct2_diag (c : Ix r s) (P : Pol p q r s) (m : Ln p q r s →₀ ℕ) :
    coeff m (fockAct2 p q r s (Eab c c) P) =
      (((wt2 m c : ℚ) + sh2 p q r s c : ℚ) : ℂ) * coeff m P := by sorry
