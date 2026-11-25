-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ScGapBig_nat_bound
-- name    : PI.UnitaryGroupMassFormula.ScGapBig.nat_bound
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:33:01.205482+00:00
-- url     : https://prove2.me/theorems/97c1a48e-23b9-4e5e-90f9-86612509d07c
-- title:
--   Sc Gap Big: nat bound
-- statement:
--   The Sc Gap Big construction uses the nat bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SpectralGapLarge/ScGapBigMain.lean#L8-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SpectralGapLarge/ScGapBigMain.lean#L8-L20

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScGapBig
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SpectralGapLarge_ScGapBigMain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScGapBig
open PI.ScGapBig

theorem PI.UnitaryGroupMassFormula.ScGapBig.nat_bound (n m t : ℕ) (hn : 1801 ≤ n) (hm : m ≤ n + 1) (ht : t ≤ n + 6) :
    2 * (n + m * t) ^ 3 + t + 3 < 16 * n ^ 19 := by sorry
