-- Prove2me | Theorems.Thm_PI_CMT_coe_conj
-- name    : PI.CMT.coe_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:00:24.771872+00:00
-- url     : https://prove2.me/theorems/34db84f2-60e5-4d35-9ab2-4b0cd4773eb5
-- title:
--   CMT: coe conj
-- statement:
--   The CMT construction uses the coe conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMTraceSurjective/IsTrMulConjOfMem.lean#L14-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMTraceSurjective/IsTrMulConjOfMem.lean#L14-L14

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CMTraceOnto
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMTraceSurjective_IsTrMulConjOfMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CMT
open NumberField
variable {K : Type*} [Field K] [StarRing K]

theorem PI.CMT.coe_conj (x : 𝓞 K) : ((conj x : 𝓞 K) : K) = star (x : K) := by sorry
