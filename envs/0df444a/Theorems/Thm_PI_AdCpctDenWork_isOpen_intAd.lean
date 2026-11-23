-- Prove2me | Theorems.Thm_PI_AdCpctDenWork_isOpen_intAd
-- name    : PI.AdCpctDenWork.isOpen_intAd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:53.234729+00:00
-- url     : https://prove2.me/theorems/81d496c4-8025-4085-9724-8239129790ec
-- title:
--   Ad Cpct Den Work: is Open int Ad
-- statement:
--   The Ad Cpct Den Work construction uses the is Open int Ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdicCompactDensity/ExistsNatLocal.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdicCompactDensity/ExistsNatLocal.lean#L17-L18

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

theorem PI.AdCpctDenWork.isOpen_intAd : IsOpen (intAd F) := by sorry
