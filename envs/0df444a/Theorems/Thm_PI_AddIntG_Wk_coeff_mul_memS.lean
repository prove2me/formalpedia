-- Prove2me | Theorems.Thm_PI_AddIntG_Wk_coeff_mul_memS
-- name    : PI.AddIntG.Wk.coeff_mul_memS
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:22:12.032988+00:00
-- url     : https://prove2.me/theorems/97ad70e4-14e5-4ad3-94e1-733da2d00777
-- title:
--   Wk: coeff mul mem S
-- statement:
--   The Wk construction uses the coeff mul mem S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/CoeffPowMemS.lean#L17-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/CoeffPowMemS.lean#L17-L25

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GuLine
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffPowMemS
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

theorem PI.AddIntG.Wk.coeff_mul_memS {S : Subring ℂ_[p]} {f g : PowerSeries ℂ_[p]} {m : ℕ}
    (hf : ∀ i ≤ m, PowerSeries.coeff i f ∈ S) (hg : ∀ i ≤ m, PowerSeries.coeff i g ∈ S) :
    PowerSeries.coeff m (f * g) ∈ S := by sorry
