-- Prove2me | Theorems.Thm_PI_AddIntG_Wk_mvsubst_mem_SerS
-- name    : PI.AddIntG.Wk.mvsubst_mem_SerS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:58.754992+00:00
-- url     : https://prove2.me/theorems/dd5f2424-0a8e-45b3-8679-82f6db5a8569
-- title:
--   Wk: mvsubst mem Ser S
-- statement:
--   The Wk construction uses the mvsubst mem Ser S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/SubstMem.lean#L46-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/SubstMem.lean#L46-L64

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

theorem PI.AddIntG.Wk.mvsubst_mem_SerS {K : Type*} [CommRing K] (S : Subring K) {σ τ : Type*} [Finite σ]
    {a : σ → MvPowerSeries τ K} {f : MvPowerSeries σ K} (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (ha : ∀ i, a i ∈ SerS S τ) (hf : f ∈ SerS S σ) : MvPowerSeries.subst a f ∈ SerS S τ := by sorry
