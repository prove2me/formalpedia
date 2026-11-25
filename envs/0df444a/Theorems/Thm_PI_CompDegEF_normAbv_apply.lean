-- Prove2me | Theorems.Thm_PI_CompDegEF_normAbv_apply
-- name    : PI.CompDegEF.normAbv_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:30:48.361975+00:00
-- url     : https://prove2.me/theorems/986769e3-5a80-4f77-a602-4d802d96dc5f
-- title:
--   Comp Deg EF: norm Abv apply
-- statement:
--   The Comp Deg EF construction uses the norm Abv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompletionDegrees/IsEquivAdicAbvNormAbv.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompletionDegrees/IsEquivAdicAbvNormAbv.lean#L15-L16

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_NormLeOneOfInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_IsEquivAdicAbvNormAbv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.CompDegEF
open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem PI.CompDegEF.normAbv_apply {l : ℕ} [Fact l.Prime] {E : Type} [Field E] (φ : E →+* Om l) (x : E) :
    normAbv φ x = ‖φ x‖ := by sorry
