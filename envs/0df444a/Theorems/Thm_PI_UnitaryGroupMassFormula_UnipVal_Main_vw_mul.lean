-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnipVal_Main_vw_mul
-- name    : PI.UnitaryGroupMassFormula.UnipVal.Main.vw_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:52:28.939246+00:00
-- url     : https://prove2.me/theorems/2a64a173-ab8e-4a21-a495-7fd7e4e9616b
-- title:
--   Main: vw mul
-- statement:
--   The Main construction uses the vw mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentValuation/VwIntEqZero.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentValuation/VwIntEqZero.lean#L14-L19

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnipVal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentValuation_VwIntEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnipVal PI.UnitaryGroupMassFormula.UnipVal.Main
open PI.UnipVal
variable {K : Type} [Field K] [NumberField K]

theorem PI.UnitaryGroupMassFormula.UnipVal.Main.vw_mul (w : HeightOneSpectrum (𝓞 K)) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    vw w (x * y) = vw w x + vw w y := by sorry
