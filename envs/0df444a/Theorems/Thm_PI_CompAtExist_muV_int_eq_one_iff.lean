-- Prove2me | Theorems.Thm_PI_CompAtExist_muV_int_eq_one_iff
-- name    : PI.CompAtExist.muV_int_eq_one_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:26:41.805833+00:00
-- url     : https://prove2.me/theorems/ff684817-fcb2-42be-9769-0ee5859c184b
-- title:
--   Comp At Exist: mu V int eq one iff
-- statement:
--   The Comp At Exist construction uses the mu V int eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompletionExistence/LeOneIffOfMulEqOne.lean#L104-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompletionExistence/LeOneIffOfMulEqOne.lean#L104-L107

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_AdelicCompactOpens_UniROfUniRT
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionExistence_LeOneIffOfMulEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CompAtExist
open NumberField IsDedekindDomain ReciprocityTheory.Aut
variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem PI.CompAtExist.muV_int_eq_one_iff (s : SplitPlace L) (r : 𝓞 L) :
    muV s (algebraMap (𝓞 L) L r) = 1 ↔ r ∉ s.w.asIdeal := by sorry
