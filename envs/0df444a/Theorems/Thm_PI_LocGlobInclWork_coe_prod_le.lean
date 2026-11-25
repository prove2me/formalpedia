-- Prove2me | Theorems.Thm_PI_LocGlobInclWork_coe_prod_le
-- name    : PI.LocGlobInclWork.coe_prod_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:35:14.846338+00:00
-- url     : https://prove2.me/theorems/44951016-973e-46c1-b954-801bf6006957
-- title:
--   Loc Glob Incl Work: coe prod le
-- statement:
--   The Loc Glob Incl Work construction uses the coe prod le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalGlobalInclusion/SmulMemIdealSmul.lean#L60-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalGlobalInclusion/SmulMemIdealSmul.lean#L60-L74

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

theorem PI.LocGlobInclWork.coe_prod_le (S : Finset (HeightOneSpectrum (𝓞 K))) (n : HeightOneSpectrum (𝓞 K) → ℤ) :
    ((∏ v ∈ S, v.asIdeal ^ (n v).toNat : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≤
      ∏ v ∈ S, (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ n v := by sorry
