-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_isK_sum
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.isK_sum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:34:32.638883+00:00
-- url     : https://prove2.me/theorems/bb963d90-1beb-49fc-b756-f15b4c57f578
-- title:
--   Unimod Loc Std: is K sum
-- statement:
--   The Unimod Loc Std construction uses the is K sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/IsKTheta.lean#L106-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/IsKTheta.lean#L106-L113

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_SelfDualStd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_IsKTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable (b : ℤ) (d : ℕ)
variable {b d}
variable {e : ℤ} (hn : cmTheta b d * (b - cmTheta b d) = (e : ℂ))
include hn

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.isK_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) (hf : ∀ i ∈ s, IsK b d (f i)) : IsK b d (∑ i ∈ s, f i) := by sorry
