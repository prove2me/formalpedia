-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_GramIso_be_zero_left
-- name    : PI.UnitaryGroupMassFormula.GramIso.be_zero_left
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:38:42.157955+00:00
-- url     : https://prove2.me/theorems/a45d85dc-30b6-41bd-85af-3fed18f8b3fa
-- title:
--   Gram Iso: be zero left
-- statement:
--   The Gram Iso construction uses the be zero left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramIsometryCoefficient/ExCoeffOneNe.lean#L53-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramIsometryCoefficient/ExCoeffOneNe.lean#L53-L63

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramIsometryCoefficient_ExCoeffOneNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.GramIso
open PI.FglGram
variable {p : ℕ} [Fact p.Prime]

theorem PI.UnitaryGroupMassFormula.GramIso.be_zero_left (l ex ph : PowerSeries ℂ_[p]) (hD : Data l ex ph) {r : ℕ} (j j' : Fin r) :
    be l ex ph (mulBy l ex 0 (Xv j)) (Xv j' : MvPowerSeries (Fin r) ℂ_[p]) = 0 := by sorry
