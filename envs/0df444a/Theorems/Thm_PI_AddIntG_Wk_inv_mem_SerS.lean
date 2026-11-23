-- Prove2me | Theorems.Thm_PI_AddIntG_Wk_inv_mem_SerS
-- name    : PI.AddIntG.Wk.inv_mem_SerS
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:52:21.235534+00:00
-- url     : https://prove2.me/theorems/d337e2fa-29a4-4e3e-aac0-c396da07439c
-- title:
--   Wk: inv mem Ser S
-- statement:
--   The Wk construction uses the inv mem Ser S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/SubstMem.lean#L33-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/SubstMem.lean#L33-L44

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

theorem PI.AddIntG.Wk.inv_mem_SerS {K : Type*} [Field K] (S : Subring K) {σ : Type*} {f : MvPowerSeries σ K}
    (h0 : MvPowerSeries.constantCoeff f = 1) (hf : f ∈ SerS S σ) : f⁻¹ ∈ SerS S σ := by sorry
