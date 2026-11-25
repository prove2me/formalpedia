-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_ZI_contDiffOn_cF
-- name    : PI.UnitaryGroupMassFormula.UsCost.ZI.contDiffOn_cF
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:41:27.687938+00:00
-- url     : https://prove2.me/theorems/865ddaec-7ea2-40c2-967e-89136319b32a
-- title:
--   ZI: cont Diff On c F
-- statement:
--   The ZI construction uses the cont Diff On c F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ZIterB.lean#L97-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ZIterB.lean#L97-L103

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

theorem PI.UnitaryGroupMassFormula.UsCost.ZI.contDiffOn_cF (i : Fin s × Fin s × Bool) (n : ℕ) :
    ContDiffOn ℝ n (cF s i) {Z : Fin s → Fin s → ℂ | (Matrix.of Z).det ≠ 0} := by sorry
