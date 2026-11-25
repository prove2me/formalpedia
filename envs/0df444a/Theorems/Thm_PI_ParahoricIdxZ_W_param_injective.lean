-- Prove2me | Theorems.Thm_PI_ParahoricIdxZ_W_param_injective
-- name    : PI.ParahoricIdxZ.W.param_injective
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:35:48.799543+00:00
-- url     : https://prove2.me/theorems/f79052db-4fd9-511a-9ba3-d91db6cc04ef
-- title:
--   W: param injective
-- statement:
--   The W construction uses the param injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/ParamInjective.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/ParamInjective.lean#L21-L28

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_CardRangeRedJ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_ParamInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures.P.GLRed
open PI PI.ParahoricIdxZ PI.ParahoricIdxZ.W
variable {F : Type} [Field F] (O : Subring F) {ϖ : F} (hϖ : ϖ ∈ O)

theorem PI.ParahoricIdxZ.W.param_injective {a t : ℕ} (J' : Subgroup (GL (Fin a) F)) (hJ : J' ≤ Formalism.DoubleCosetMeasures.GLint O a) :
    Function.Injective (param (t := t) O hϖ J' hJ) := by sorry
