-- Prove2me | Theorems.Thm_P2M_HalfIntGap__gap_673ecf939950
-- name    : P2M_HalfIntGap__gap_673ecf939950
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:55:10.200205+00:00
-- url     : https://prove2.me/theorems/0315c8be-3ebf-4ec1-be9e-c91d5e533b23
-- title:
--   P2 M Half Int Gap  gap 673ecf939950: P2 M Half Int Gap  gap 673ecf939950
-- statement:
--   The P2 M Half Int Gap  gap 673ecf939950 construction uses the P2 M Half Int Gap  gap 673ecf939950 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HalfIntegerGap/IntGap.lean#L25-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HalfIntegerGap/IntGap.lean#L25-L45

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

theorem P2M_HalfIntGap__gap_673ecf939950 (N : ℕ) (lam : Fin N → ℝ) (c : ℝ) (hlam : StrictAnti lam)
    (hc : ∀ a, ∃ m : ℤ, lam a - c = m) (a b : Fin N) (hab : a < b) :
    ((b.val : ℝ) - a.val) ≤ lam a - lam b := by sorry

alias «HalfIntGap₂».«gap» := P2M_HalfIntGap__gap_673ecf939950
