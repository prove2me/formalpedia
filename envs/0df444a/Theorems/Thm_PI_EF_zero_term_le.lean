-- Prove2me | Theorems.Thm_PI_EF_zero_term_le
-- name    : PI.EF.zero_term_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:35.21116+00:00
-- url     : https://prove2.me/theorems/07f8f5f2-6411-5dc3-aa04-64836076b2ca
-- title:
--   EF: zero term le
-- statement:
--   The EF construction uses the zero term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/NormSubCtrSq.lean#L120-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/NormSubCtrSq.lean#L120-L154

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_HalfLeNormLentCtr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_NormSubCtrSq
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
open Complex Metric Filter Topology Set DirichletCharacter
variable {N : ℕ} [NeZero N]

theorem PI.EF.zero_term_le (hZL : ZeroLocus) {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {t : ℝ}
    (s : ℂ) (hs : s.im = t) :
    ‖(open Classical in if (0 : ℂ) ∈ DZ χ t then (mult χ 0 : ℂ) / (s - 0) else 0) - eps0 χ / s‖
      ≤ 1 := by sorry
