-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_GramIso_ex_comp_l
-- name    : PI.UnitaryGroupMassFormula.GramIso.ex_comp_l
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:38:37.189899+00:00
-- url     : https://prove2.me/theorems/24eea5ae-344c-4884-b627-2e7efd772326
-- title:
--   Gram Iso: ex comp l
-- statement:
--   The Gram Iso construction uses the ex comp l property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramIsometryCoefficient/ExCoeffOneNe.lean#L37-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramIsometryCoefficient/ExCoeffOneNe.lean#L37-L51

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

theorem PI.UnitaryGroupMassFormula.GramIso.ex_comp_l (l ex : PowerSeries ℂ_[p]) (he : PowerSeries.constantCoeff ex = 0)
    (hl : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.subst l ex = PowerSeries.X := by sorry
