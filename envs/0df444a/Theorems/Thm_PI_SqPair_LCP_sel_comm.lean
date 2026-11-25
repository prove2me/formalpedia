-- Prove2me | Theorems.Thm_PI_SqPair_LCP_sel_comm
-- name    : PI.SqPair.LCP.sel_comm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:23:49.336386+00:00
-- url     : https://prove2.me/theorems/9c25f6fa-05c3-464c-8bfc-f92699d2cb10
-- title:
--   LCP: sel comm
-- statement:
--   The LCP construction uses the sel comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/SelCore.lean#L92-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/SelCore.lean#L92-L113

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_SelCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SqPair PI.SqPair.LCP
variable {R : Type} [CommRing R] [IsDomain R]

theorem PI.SqPair.LCP.sel_comm {ι : Type} [Fintype ι] [DecidableEq ι] {c : R} (hc : c ≠ 0)
    (g h : Matrix ι ι R) (hgh : g * h = c • 1) : h * g = c • 1 := by sorry
