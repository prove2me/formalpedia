-- Prove2me | Theorems.Thm_PI_adCpctDen
-- name    : PI.adCpctDen
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:46:56.280782+00:00
-- url     : https://prove2.me/theorems/f59de156-5ee0-4992-88d4-05e53a86d01c
-- title:
--   PI: ad Cpct Den
-- statement:
--   The PI construction uses the ad Cpct Den property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdicCompactDensity/ExistsNatLocal.lean#L63-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdicCompactDensity/ExistsNatLocal.lean#L63-L92

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

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum PI.AdCpctDenWork

theorem PI.adCpctDen : PI.AdCpctDen := by sorry
