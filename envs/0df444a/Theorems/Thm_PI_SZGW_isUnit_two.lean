-- Prove2me | Theorems.Thm_PI_SZGW_isUnit_two
-- name    : PI.SZGW.isUnit_two
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:37:08.421049+00:00
-- url     : https://prove2.me/theorems/da7d76ed-2949-47d6-be87-e5a682a1591b
-- title:
--   SZGW: is Unit two
-- statement:
--   The SZGW construction uses the is Unit two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitZeroClosedness/IsClosedSimeqZero.lean#L44-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitZeroClosedness/IsClosedSimeqZero.lean#L44-L54

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitZeroClosedness_ZcFacts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitZeroClosedness_IsClosedSimeqZero
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
open PI PI.SZGW
open PI.BeDiagZp.ContPf

theorem PI.SZGW.isUnit_two {p : ℕ} [hp : Fact p.Prime] (h2 : p ≠ 2) : IsUnit (2 : ℤ_[p]) := by sorry
