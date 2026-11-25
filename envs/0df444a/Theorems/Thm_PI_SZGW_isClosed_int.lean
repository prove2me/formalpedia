-- Prove2me | Theorems.Thm_PI_SZGW_isClosed_int
-- name    : PI.SZGW.isClosed_int
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:37:17.51256+00:00
-- url     : https://prove2.me/theorems/9d6b9e35-d57c-455c-8d48-f9d43a4237b4
-- title:
--   SZGW: is Closed int
-- statement:
--   The SZGW construction uses the is Closed int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitZeroClosedness/IsClosedSimeqZero.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitZeroClosedness/IsClosedSimeqZero.lean#L21-L24

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

theorem PI.SZGW.isClosed_int {p : ℕ} [Fact p.Prime] {σ : Type} {G : ℂ_[p] → MvPowerSeries σ ℂ_[p]}
    (hG : CC G) : IsClosed {c : ℂ_[p] | PI.BeDiagZp.IntegralMv (G c)} := by sorry
