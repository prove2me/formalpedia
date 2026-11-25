-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_ZI_cF_apply
-- name    : PI.UnitaryGroupMassFormula.UsCost.ZI.cF_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:41:27.432359+00:00
-- url     : https://prove2.me/theorems/96e20cae-efe7-4671-86e5-2efcd7719c51
-- title:
--   ZI: c F apply
-- statement:
--   The ZI construction uses the c F apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ZIterB.lean#L81-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ZIterB.lean#L81-L92

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.ZI
variable (s : ℕ)

theorem PI.UnitaryGroupMassFormula.UsCost.ZI.cF_apply (i : Fin s × Fin s × Bool) {Z : Fin s → Fin s → ℂ} (h : (Matrix.of Z).det ≠ 0)
    (W : Fin s → Fin s → ℂ) :
    cF s i Z W = if i.2.2 then (((Matrix.of Z)⁻¹ * Matrix.of W) i.1 i.2.1).re
      else (((Matrix.of Z)⁻¹ * Matrix.of W) i.1 i.2.1).im := by sorry
