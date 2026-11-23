-- Prove2me | Theorems.Thm_PI_AddIntG_Wk_mem_SerS
-- name    : PI.AddIntG.Wk.mem_SerS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:51.793009+00:00
-- url     : https://prove2.me/theorems/45f90ed4-84ca-4d99-a5a5-5b86a87728d5
-- title:
--   Wk: mem Ser S
-- statement:
--   The Wk construction uses the mem Ser S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/SubstMem.lean#L10-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/SubstMem.lean#L10-L20

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

theorem PI.AddIntG.Wk.mem_SerS {K : Type*} [CommRing K] (S : Subring K) {σ : Type*} (f : MvPowerSeries σ K) :
    f ∈ SerS S σ ↔ ∀ e, MvPowerSeries.coeff e f ∈ S := by sorry
