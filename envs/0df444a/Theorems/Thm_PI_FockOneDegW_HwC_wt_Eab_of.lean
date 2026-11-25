-- Prove2me | Theorems.Thm_PI_FockOneDegW_HwC_wt_Eab_of
-- name    : PI.FockOneDegW.HwC.wt_Eab_of
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:30:55.441772+00:00
-- url     : https://prove2.me/theorems/06c18599-fe46-58f8-9a9e-e79d0cf76c96
-- title:
--   Hw C: wt Eab of
-- statement:
--   The Hw C construction uses the wt Eab of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/CoeffXMulPderivSelf.lean#L159-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/CoeffXMulPderivSelf.lean#L159-L165

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_FockOperatorsKernel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_CoeffXMulPderivSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FockOneDegW PI.FockOneDegW.HwC

theorem PI.FockOneDegW.HwC.wt_Eab_of {p q r s : ℕ} {ν : Ix p q → ℚ} {P : Pol p q r s} (hP : IsWt ν P)
    (a b : Ix p q) (hab : sameBlock a b) (hne : a ≠ b) :
    IsWt (fun c => ν c + (if a = c then 1 else 0) - (if b = c then 1 else 0))
      (fockAct1 p q r s (Eab a b) P) := by sorry
