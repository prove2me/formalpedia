-- Prove2me | Theorems.Thm_PI_AdCpctDenWork_natCast_mem_int
-- name    : PI.AdCpctDenWork.natCast_mem_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:46.758735+00:00
-- url     : https://prove2.me/theorems/97665013-9cce-4a62-9bc2-c1ee84d1d217
-- title:
--   Ad Cpct Den Work: nat Cast mem int
-- statement:
--   The Ad Cpct Den Work construction uses the nat Cast mem int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdicCompactDensity/ExistsNatLocal.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdicCompactDensity/ExistsNatLocal.lean#L24-L26

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

theorem PI.AdCpctDenWork.natCast_mem_int (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    (n : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by sorry
