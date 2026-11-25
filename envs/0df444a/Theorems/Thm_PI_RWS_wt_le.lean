-- Prove2me | Theorems.Thm_PI_RWS_wt_le
-- name    : PI.RWS.wt_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:19:02.644296+00:00
-- url     : https://prove2.me/theorems/1994ad68-ae0c-547e-b29f-3f176795d230
-- title:
--   RWS: wt le
-- statement:
--   The RWS construction uses the wt le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RowWeightSpan/RowWtSpanOfBideterminant.lean#L51-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RowWeightSpan/RowWtSpanOfBideterminant.lean#L51-L66

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RowWtSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowWeightSpan_RowWtSpanOfBideterminant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.RWS
open PI.RW

theorem PI.RWS.wt_le {k N : ℕ} (sz : Fin N → ℕ) (I : ∀ j, Fin (sz j) → Fin k)
    (hI : ∀ j, StrictMono (I j)) (a t0 : Fin k) (ht0 : t0.val = 0) :
    ∑ j, (Finset.univ.filter fun p => I j p = a).card ≤ shapeDeg sz t0 := by sorry
