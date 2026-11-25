-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnipVal_Main_vw_int_eq_zero
-- name    : PI.UnitaryGroupMassFormula.UnipVal.Main.vw_int_eq_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:41:46.496311+00:00
-- url     : https://prove2.me/theorems/a3122f43-3311-4c19-95c9-81b6b95c3e46
-- title:
--   Main: vw int eq zero
-- statement:
--   The Main construction uses the vw int eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentValuation/VwIntEqZero.lean#L25-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentValuation/VwIntEqZero.lean#L25-L36

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

theorem PI.UnitaryGroupMassFormula.UnipVal.Main.vw_int_eq_zero (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (hx : x ≠ 0)
    (hxw : x ∉ w.asIdeal) : vw w (algebraMap (𝓞 K) K x) = 0 := by sorry
