-- Prove2me | Theorems.Thm_P2M_PI_FglTriFactor_Wk_abel__b380fdd8500c
-- name    : P2M_PI_FglTriFactor_Wk_abel__b380fdd8500c
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:56:48.732358+00:00
-- url     : https://prove2.me/theorems/5c213595-f335-4cc2-af34-ed1dbf664398
-- title:
--   P2 M PI Fgl Tri Factor Wk abel  b380fdd8500c: P2 M PI Fgl Tri Factor Wk abel  b380fdd8500c
-- statement:
--   The P2 M PI Fgl Tri Factor Wk abel  b380fdd8500c construction uses the P2 M PI Fgl Tri Factor Wk abel  b380fdd8500c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/LogThirdPointSum.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/LogThirdPointSum.lean#L20-L22

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

theorem P2M_PI_FglTriFactor_Wk_abel__b380fdd8500c {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    lg (flog W wq) (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) + lg (flog W wq) (MvPowerSeries.X 1) +
      lg (flog W wq) (Z3 W wq) = 0 := by sorry

alias «PI».«FglTriFactor».«Wk».«abel'» := P2M_PI_FglTriFactor_Wk_abel__b380fdd8500c
