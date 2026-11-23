-- Prove2me | Theorems.Thm_PI_AdCpctDenWork_exists_nat_adele
-- name    : PI.AdCpctDenWork.exists_nat_adele
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:27.162616+00:00
-- url     : https://prove2.me/theorems/036fe331-a1a7-43de-8ab2-4836102003c1
-- title:
--   Ad Cpct Den Work: exists nat adele
-- statement:
--   The Ad Cpct Den Work construction uses the exists nat adele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdicCompactDensity/ExistsNatLocal.lean#L42-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdicCompactDensity/ExistsNatLocal.lean#L42-L57

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

theorem PI.AdCpctDenWork.exists_nat_adele (a : FiniteAdeleRing (𝓞 F) F) :
    ∃ n : ℕ, 0 < n ∧ (n : FiniteAdeleRing (𝓞 F) F) * a ∈ intAd F := by sorry
