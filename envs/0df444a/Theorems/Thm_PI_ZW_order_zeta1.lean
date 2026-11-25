-- Prove2me | Theorems.Thm_PI_ZW_order_zeta1
-- name    : PI.ZW.order_zeta1
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:46:50.776118+00:00
-- url     : https://prove2.me/theorems/4808f978-6714-4a96-abb4-61749ab1ecd7
-- title:
--   ZW: order zeta1
-- statement:
--   The ZW construction uses the order zeta1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/RightOne.lean#L26-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/RightOne.lean#L26-L39

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightChi
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Metric Complex Filter Topology
open PI PI.ZW

theorem PI.ZW.order_zeta1 {s : ℂ} (hs : s ≠ 1) :
    analyticOrderNatAt zeta1 s = analyticOrderNatAt riemannZeta s := by sorry
