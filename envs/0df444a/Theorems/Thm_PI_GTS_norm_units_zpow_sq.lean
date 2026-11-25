-- Prove2me | Theorems.Thm_PI_GTS_norm_units_zpow_sq
-- name    : PI.GTS.norm_units_zpow_sq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:31:24.415537+00:00
-- url     : https://prove2.me/theorems/6444aa43-b2fa-4ab4-a1a0-7232069bf1f3
-- title:
--   GTS: norm units zpow sq
-- statement:
--   The GTS construction uses the norm units zpow sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitPowerNormScale/NormUnitsZpowSq.lean#L37-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitPowerNormScale/NormUnitsZpowSq.lean#L37-L42

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GTScale
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitPowerNormScale_NormUnitsZpowSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GTS
open Formalism.BasicNotions MvPolynomial

theorem PI.GTS.norm_units_zpow_sq (u : ℂˣ) (e : ℤ) :
    ‖((u ^ e : ℂˣ) : ℂ)‖ ^ 2 = ‖(u : ℂ)‖ ^ (2 * e) := by sorry
