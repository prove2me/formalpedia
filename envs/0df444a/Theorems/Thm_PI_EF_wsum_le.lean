-- Prove2me | Theorems.Thm_PI_EF_wsum_le
-- name    : PI.EF.wsum_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:25:31.964724+00:00
-- url     : https://prove2.me/theorems/e5ee2426-3a7e-467c-b17a-4ee378ac0222
-- title:
--   EF: wsum le
-- statement:
--   The EF construction uses the wsum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/GoodHeight.lean#L94-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/GoodHeight.lean#L94-L103

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open DirichletCharacter

theorem PI.EF.wsum_le {C : ℝ} (hC0 : 0 ≤ C) (hC : ZerosWindowWith C) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) {T t : ℝ} (_hT : 0 ≤ T) (ht : |t| ≤ T + 1) :
    wsum χ t ≤ C * Real.log (N * (T + 3)) := by sorry
