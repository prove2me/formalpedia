-- Prove2me | Theorems.Thm_PI_WFJM_coeff_fockAct1_diag
-- name    : PI.WFJM.coeff_fockAct1_diag
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:44:11.559507+00:00
-- url     : https://prove2.me/theorems/9ea95cb6-e58d-4f00-8158-9b5de7b6ad06
-- title:
--   WFJM: coeff fock Act1 diag
-- statement:
--   The WFJM construction uses the coeff fock Act1 diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L599-L608
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L599-L608

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

theorem PI.WFJM.coeff_fockAct1_diag (a : Ix p q) (P : Pol p q r s) (m : Ln p q r s →₀ ℕ) :
    coeff m (fockAct1 p q r s (Eab a a) P) =
      (((wt1 m a : ℚ) + sh1 p q r s a : ℚ) : ℂ) * coeff m P := by sorry
