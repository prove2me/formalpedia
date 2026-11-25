-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_GramIso_ex_coeff_one_ne
-- name    : PI.UnitaryGroupMassFormula.GramIso.ex_coeff_one_ne
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:38:28.388259+00:00
-- url     : https://prove2.me/theorems/5c41cd31-7f24-423f-a9b9-dd0a9eb197ea
-- title:
--   Gram Iso: ex coeff one ne
-- statement:
--   The Gram Iso construction uses the ex coeff one ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramIsometryCoefficient/ExCoeffOneNe.lean#L22-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramIsometryCoefficient/ExCoeffOneNe.lean#L22-L35

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

theorem PI.UnitaryGroupMassFormula.GramIso.ex_coeff_one_ne (l ex : PowerSeries ℂ_[p]) (he : PowerSeries.constantCoeff ex = 0)
    (hl : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.coeff 1 ex ≠ 0 := by sorry
