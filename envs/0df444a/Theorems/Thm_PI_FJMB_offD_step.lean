-- Prove2me | Theorems.Thm_PI_FJMB_offD_step
-- name    : PI.FJMB.offD_step
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:52.272799+00:00
-- url     : https://prove2.me/theorems/44750853-7b92-4daf-89c5-9b1e8024ead7
-- title:
--   FJMB: off D step
-- statement:
--   The FJMB construction uses the off D step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurElim.lean#L92-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurElim.lean#L92-L108

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Classical
open PI PI.FJMB
variable {σ : Type*}
variable {m n : ℕ} (ι : Fin (m + 1) × Fin (n + 1) → σ) (hι : Function.Injective ι)
include hι

theorem PI.FJMB.offD_step : offD (fun x : Fin m × Fin n => ι (x.1.succ, x.2.succ)) ∪ edge ι = offD ι := by sorry
