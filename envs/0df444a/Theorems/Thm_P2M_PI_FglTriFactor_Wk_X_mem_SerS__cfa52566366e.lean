-- Prove2me | Theorems.Thm_P2M_PI_FglTriFactor_Wk_X_mem_SerS__cfa52566366e
-- name    : P2M_PI_FglTriFactor_Wk_X_mem_SerS__cfa52566366e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:52:50.845518+00:00
-- url     : https://prove2.me/theorems/5c6ed9dc-27c6-460e-80c3-e47266712c9b
-- title:
--   P2 M PI Fgl Tri Factor Wk X mem Ser S  cfa52566366e: P2 M PI Fgl Tri Factor Wk X mem Ser S  cfa52566366e
-- statement:
--   The P2 M PI Fgl Tri Factor Wk X mem Ser S  cfa52566366e construction uses the P2 M PI Fgl Tri Factor Wk X mem Ser S  cfa52566366e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/CoeffSubstUpdZero.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/CoeffSubstUpdZero.lean#L31-L37

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_CoeffSubstUpdZero
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
open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS)
variable {K : Type*} [Field K] {σ : Type*} [Finite σ] [DecidableEq σ]

theorem P2M_PI_FglTriFactor_Wk_X_mem_SerS__cfa52566366e (S : Subring K) (i : σ) : (MvPowerSeries.X i : MvPowerSeries σ K) ∈ SerS S σ := by sorry

alias «PI».«FglTriFactor».«Wk».«X_mem_SerS'» := P2M_PI_FglTriFactor_Wk_X_mem_SerS__cfa52566366e
