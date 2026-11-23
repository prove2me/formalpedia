-- Prove2me | Theorems.Thm_PI_AdCpctDenWork_natCast_mul_apply
-- name    : PI.AdCpctDenWork.natCast_mul_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:44.881062+00:00
-- url     : https://prove2.me/theorems/e6e75a03-db79-4eee-903c-5cf830690d37
-- title:
--   Ad Cpct Den Work: nat Cast mul apply
-- statement:
--   The Ad Cpct Den Work construction uses the nat Cast mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdicCompactDensity/ExistsNatLocal.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdicCompactDensity/ExistsNatLocal.lean#L20-L22

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdCpctDen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicCompactDensity_ExistsNatLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.AdCpctDenWork
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {F : Type} [Field F] [NumberField F]

theorem PI.AdCpctDenWork.natCast_mul_apply (n : ℕ) (a : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    ((n : FiniteAdeleRing (𝓞 F) F) * a) v = (n : v.adicCompletion F) * a v := by sorry
