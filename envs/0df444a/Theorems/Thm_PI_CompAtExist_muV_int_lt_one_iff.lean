-- Prove2me | Theorems.Thm_PI_CompAtExist_muV_int_lt_one_iff
-- name    : PI.CompAtExist.muV_int_lt_one_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:58.004821+00:00
-- url     : https://prove2.me/theorems/2630904a-0933-430c-9693-ced78c54e1b9
-- title:
--   Comp At Exist: mu V int lt one iff
-- statement:
--   The Comp At Exist construction uses the mu V int lt one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompletionExistence/LeOneIffOfMulEqOne.lean#L100-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompletionExistence/LeOneIffOfMulEqOne.lean#L100-L102

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

theorem PI.CompAtExist.muV_int_lt_one_iff (s : SplitPlace L) (r : 𝓞 L) :
    muV s (algebraMap (𝓞 L) L r) < 1 ↔ r ∈ s.w.asIdeal := by sorry
