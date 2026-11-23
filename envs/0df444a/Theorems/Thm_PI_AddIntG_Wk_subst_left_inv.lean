-- Prove2me | Theorems.Thm_PI_AddIntG_Wk_subst_left_inv
-- name    : PI.AddIntG.Wk.subst_left_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:57:20.755796+00:00
-- url     : https://prove2.me/theorems/67f83acf-2ed0-4d32-afa6-6fbea7b3365a
-- title:
--   Wk: subst left inv
-- statement:
--   The Wk construction uses the subst left inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/GlueHoldsVar.lean#L187-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/GlueHoldsVar.lean#L187-L206

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GuLine
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GlueHoldsVar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.AddIntG PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]

theorem PI.AddIntG.Wk.subst_left_inv {K : Type*} [Field K] {l ex : PowerSeries K} (hl0 : PowerSeries.constantCoeff l = 0)
    (hl1 : PowerSeries.coeff 1 l = 1) (hex0 : PowerSeries.constantCoeff ex = 0)
    (h : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.subst l ex = PowerSeries.X := by sorry
