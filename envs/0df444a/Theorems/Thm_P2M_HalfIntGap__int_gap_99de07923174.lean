-- Prove2me | Theorems.Thm_P2M_HalfIntGap__int_gap_99de07923174
-- name    : P2M_HalfIntGap__int_gap_99de07923174
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:55:23.421714+00:00
-- url     : https://prove2.me/theorems/6c368481-e18e-40a1-a6e5-61bc1f951769
-- title:
--   P2 M Half Int Gap  int gap 99de07923174: P2 M Half Int Gap  int gap 99de07923174
-- statement:
--   The P2 M Half Int Gap  int gap 99de07923174 construction uses the P2 M Half Int Gap  int gap 99de07923174 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HalfIntegerGap/IntGap.lean#L6-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HalfIntegerGap/IntGap.lean#L6-L23

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_UnitTraceSumBounds_CBCardNC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HalfIntegerGap_IntGap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HalfIntGap₂

theorem P2M_HalfIntGap__int_gap_99de07923174 {N : ℕ} (m : Fin N → ℤ) (hm : StrictAnti m) :
    ∀ d : ℕ, ∀ a b : Fin N, b.val = a.val + d → (d : ℤ) ≤ m a - m b := by sorry

alias «HalfIntGap₂».«int_gap» := P2M_HalfIntGap__int_gap_99de07923174
