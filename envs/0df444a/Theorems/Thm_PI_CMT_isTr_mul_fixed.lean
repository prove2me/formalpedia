-- Prove2me | Theorems.Thm_PI_CMT_isTr_mul_fixed
-- name    : PI.CMT.isTr_mul_fixed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:15:34.81564+00:00
-- url     : https://prove2.me/theorems/b1db347e-4026-41a6-b67d-1c4277deecbd
-- title:
--   CMT: is Tr mul fixed
-- statement:
--   The CMT construction uses the is Tr mul fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMTraceSurjective/IsTrMulConjOfMem.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMTraceSurjective/IsTrMulConjOfMem.lean#L35-L37

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

theorem PI.CMT.isTr_mul_fixed {b s : 𝓞 K} (hb : conj b = b) (hs : IsTr s) : IsTr (b * s) := by sorry
