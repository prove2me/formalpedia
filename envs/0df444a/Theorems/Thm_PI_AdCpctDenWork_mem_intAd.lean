-- Prove2me | Theorems.Thm_PI_AdCpctDenWork_mem_intAd
-- name    : PI.AdCpctDenWork.mem_intAd
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:36:08.311927+00:00
-- url     : https://prove2.me/theorems/30bf1324-27ad-4cc0-8337-4e6cf9bc5ff2
-- title:
--   Ad Cpct Den Work: mem int Ad
-- statement:
--   The Ad Cpct Den Work construction uses the mem int Ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdicCompactDensity/ExistsNatLocal.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdicCompactDensity/ExistsNatLocal.lean#L13-L15

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

theorem PI.AdCpctDenWork.mem_intAd (a : FiniteAdeleRing (𝓞 F) F) :
    a ∈ intAd F ↔ ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F := by sorry
