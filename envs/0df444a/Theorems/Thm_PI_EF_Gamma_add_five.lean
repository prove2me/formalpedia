-- Prove2me | Theorems.Thm_PI_EF_Gamma_add_five
-- name    : PI.EF.Gamma_add_five
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:27:57.659655+00:00
-- url     : https://prove2.me/theorems/ed3becbb-f723-4fac-9fed-0f672845ba8e
-- title:
--   EF: Gamma add five
-- statement:
--   The EF construction uses the Gamma add five property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LGrowthGamma.lean#L102-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LGrowthGamma.lean#L102-L116

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthGamma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Filter Set

theorem PI.EF.Gamma_add_five (z : ℂ) (hz : 0 < z.re) :
    Complex.Gamma (z + 5) = (z + 4) * ((z + 3) * ((z + 2) * ((z + 1) * (z * Complex.Gamma z)))) := by sorry
