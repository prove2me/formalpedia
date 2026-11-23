-- Prove2me | Theorems.Thm_PI_FglTriFactor_Wk_fact_div
-- name    : PI.FglTriFactor.Wk.fact_div
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:55:12.639834+00:00
-- url     : https://prove2.me/theorems/936e5d19-5588-48b7-994d-8395ab928357
-- title:
--   Wk: fact div
-- statement:
--   The Wk construction uses the fact div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/CoeffSubstUpdZero.lean#L90-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/CoeffSubstUpdZero.lean#L90-L134

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

theorem PI.FglTriFactor.Wk.fact_div {S : Subring K} {k : σ} {s G : MvPowerSeries σ K}
    (hs0 : MvPowerSeries.constantCoeff s = 0) (hsS : s ∈ SerS S σ)
    (hsk : ∀ t : MvPowerSeries σ K, MvPowerSeries.constantCoeff t = 0 → MvPowerSeries.subst (upd k t) s = s)
    (hG : G ∈ SerS S σ) (hz : MvPowerSeries.subst (upd k s) G = 0) :
    ∃ H ∈ SerS S σ, G = (MvPowerSeries.X k - s) * H := by sorry
