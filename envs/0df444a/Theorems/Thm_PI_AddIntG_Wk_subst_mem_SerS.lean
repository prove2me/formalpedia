-- Prove2me | Theorems.Thm_PI_AddIntG_Wk_subst_mem_SerS
-- name    : PI.AddIntG.Wk.subst_mem_SerS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:48.873911+00:00
-- url     : https://prove2.me/theorems/2ad51b24-8968-4e0c-9f59-c88892169b42
-- title:
--   Wk: subst mem Ser S
-- statement:
--   The Wk construction uses the subst mem Ser S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/SubstMem.lean#L66-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/SubstMem.lean#L66-L69

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AddIntG PI.AddIntG.Wk

theorem PI.AddIntG.Wk.subst_mem_SerS {K : Type*} [CommRing K] (S : Subring K) {τ : Type*} {a : MvPowerSeries τ K}
    {f : PowerSeries K} (ha0 : MvPowerSeries.constantCoeff a = 0) (ha : a ∈ SerS S τ)
    (hf : (f : MvPowerSeries Unit K) ∈ SerS S Unit) : PowerSeries.subst a f ∈ SerS S τ := by sorry
