-- Prove2me | Theorems.Thm_PI_CompAtExist_muV_le_one_iff
-- name    : PI.CompAtExist.muV_le_one_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:26:54.427798+00:00
-- url     : https://prove2.me/theorems/4c3fc51b-0d05-4a14-b90d-d7133750f9c1
-- title:
--   Comp At Exist: mu V le one iff
-- statement:
--   The Comp At Exist construction uses the mu V le one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompletionExistence/LeOneIffOfMulEqOne.lean#L147-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompletionExistence/LeOneIffOfMulEqOne.lean#L147-L181

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

theorem PI.CompAtExist.muV_le_one_iff (s : SplitPlace L) (x : L) : muV s x ≤ 1 ↔ s.w.valuation L x ≤ 1 := by sorry
