-- Prove2me | Theorems.Thm_PI_AddIntG_Wk_rt_G_map
-- name    : PI.AddIntG.Wk.rt_G_map
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:22:05.965288+00:00
-- url     : https://prove2.me/theorems/a4f0f675-255c-49d0-960b-c07c3f35e30b
-- title:
--   Wk: rt G map
-- statement:
--   The Wk construction uses the rt G map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/ThirdRootSubVarZeroNeZero.lean#L181-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/ThirdRootSubVarZeroNeZero.lean#L181-L184

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_ThirdRootSubVarZeroNeZero
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

theorem PI.AddIntG.Wk.rt_G_map {R R' : Type*} [CommRing R] [Algebra ℂ_[p] R] [CommRing R'] [Algebra ℂ_[p] R']
    (φ : R →ₐ[ℂ_[p]] R') (W : WeierstrassCurve ℂ_[p]) (u v : R) :
    φ (G W u v) = G W (φ u) (φ v) := by sorry
