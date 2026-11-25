-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnipVal_Main_natCast_mem_iff
-- name    : PI.UnitaryGroupMassFormula.UnipVal.Main.natCast_mem_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:41:23.098225+00:00
-- url     : https://prove2.me/theorems/d7d1c997-afff-430a-a3d0-be14df945d08
-- title:
--   Main: nat Cast mem iff
-- statement:
--   The Main construction uses the nat Cast mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentValuation/VwIntEqZero.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentValuation/VwIntEqZero.lean#L44-L46

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

theorem PI.UnitaryGroupMassFormula.UnipVal.Main.natCast_mem_iff (w : HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    ((m : 𝓞 K) ∈ w.asIdeal) ↔ plc w ∣ m := by sorry
