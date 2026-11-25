-- Prove2me | Theorems.Thm_PI_LocGlobInclWork_coe_pow_toNat_le
-- name    : PI.LocGlobInclWork.coe_pow_toNat_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:35:04.340706+00:00
-- url     : https://prove2.me/theorems/f43926aa-d2f0-5e68-b516-d4e164feba09
-- title:
--   Loc Glob Incl Work: coe pow to Nat le
-- statement:
--   The Loc Glob Incl Work construction uses the coe pow to Nat le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalGlobalInclusion/SmulMemIdealSmul.lean#L41-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalGlobalInclusion/SmulMemIdealSmul.lean#L41-L58

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocGlobIncl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalGlobalInclusion_SmulMemIdealSmul
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
open PI PI.LocGlobInclWork
variable {K : Type} [Field K] [NumberField K]

theorem PI.LocGlobInclWork.coe_pow_toNat_le (v : HeightOneSpectrum (𝓞 K)) (k : ℤ) :
    ((v.asIdeal ^ k.toNat : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≤
      (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ k := by sorry
