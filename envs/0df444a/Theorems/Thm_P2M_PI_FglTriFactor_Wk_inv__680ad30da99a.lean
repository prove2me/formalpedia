-- Prove2me | Theorems.Thm_P2M_PI_FglTriFactor_Wk_inv__680ad30da99a
-- name    : P2M_PI_FglTriFactor_Wk_inv__680ad30da99a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:11:56.582935+00:00
-- url     : https://prove2.me/theorems/35b5d3b7-6d41-4c42-b48a-3f49a06b47b3
-- title:
--   P2 M PI Fgl Tri Factor Wk inv  680ad30da99a: P2 M PI Fgl Tri Factor Wk inv  680ad30da99a
-- statement:
--   The P2 M PI Fgl Tri Factor Wk inv  680ad30da99a construction uses the P2 M PI Fgl Tri Factor Wk inv  680ad30da99a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/LogThirdPointSum.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/LogThirdPointSum.lean#L24-L27

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_SubstUpdateVarTwoLiftedThirdRoot
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GlueHoldsVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_LogThirdPointSum
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mvsubst_mem_SerS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglTriFactor PI.FglTriFactor.Wk
open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS lam nu wser wv Z3)
variable {p : ℕ} [Fact p.Prime]

theorem P2M_PI_FglTriFactor_Wk_inv__680ad30da99a {W : WeierstrassCurve ℂ_[p]} {wq ex : PowerSeries ℂ_[p]} (h : IsWq W wq)
    (hex0 : PowerSeries.constantCoeff ex = 0) (hex : PowerSeries.subst ex (flog W wq) = PowerSeries.X) :
    PowerSeries.subst (flog W wq) ex = PowerSeries.X := by sorry

alias «PI».«FglTriFactor».«Wk».«inv'» := P2M_PI_FglTriFactor_Wk_inv__680ad30da99a
