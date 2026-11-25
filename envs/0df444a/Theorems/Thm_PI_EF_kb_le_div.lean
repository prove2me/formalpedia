-- Prove2me | Theorems.Thm_PI_EF_kb_le_div
-- name    : PI.EF.kb_le_div
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:06.702944+00:00
-- url     : https://prove2.me/theorems/38ee149b-ee11-44e4-bab5-fd4ba4e7e020
-- title:
--   EF: kb le div
-- statement:
--   The EF construction uses the kb le div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronSumBound.lean#L74-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronSumBound.lean#L74-L127

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSumBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Finset

theorem PI.EF.kb_le_div {u T x g : ℝ} (hu : 0 < u) (hT : 0 < T) (hx : 0 < x) (hx2 : x < 2 * u)
    (hg : 0 < g) (h : g ≤ |u - x|) : kb T (u / x) ≤ (4 * u / T) / g := by sorry
