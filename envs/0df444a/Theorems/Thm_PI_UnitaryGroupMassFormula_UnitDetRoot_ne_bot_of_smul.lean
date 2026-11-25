-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_ne_bot_of_smul
-- name    : PI.UnitaryGroupMassFormula.UnitDetRoot.ne_bot_of_smul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:34:25.944509+00:00
-- url     : https://prove2.me/theorems/5b0542cb-df00-460c-ab5c-a125594df2a1
-- title:
--   Unit Det Root: ne bot of smul
-- statement:
--   The Unit Det Root construction uses the ne bot of smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/GlobTop.lean#L38-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/GlobTop.lean#L38-L46

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_IdealPowPrincipal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NumberField
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI Submodule NumberField

theorem PI.UnitaryGroupMassFormula.UnitDetRoot.ne_bot_of_smul {F : IntermediateField ℚ ℂ} {S T : Submodule (𝓞 F) ℂ} {c : ℂ} (hc : c ≠ 0)
    (hST : span (𝓞 F) {c} * S ≤ T) (hS : S ≠ ⊥) : T ≠ ⊥ := by sorry
