-- Prove2me | Theorems.Thm_PI_EF_far_sum_le
-- name    : PI.EF.far_sum_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:30:10.582718+00:00
-- url     : https://prove2.me/theorems/eff8dca6-ca85-4ee0-82f1-b70cb6b4ab65
-- title:
--   EF: far sum le
-- statement:
--   The EF construction uses the far sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/NormSubCtrSq.lean#L54-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/NormSubCtrSq.lean#L54-L118

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

theorem PI.EF.far_sum_le {Cw : ℝ} (hW : ZerosWindowWith Cw) (hZL : ZeroLocus) {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) {t : ℝ} (s : ℂ) (hs : s.im = t) (E : Finset ℂ)
    (hE : ∀ ρ ∈ E, ρ ∈ DZ χ t ∧ ρ ∉ ZerosNear χ t ∧ ρ ≠ 0) :
    ‖∑ ρ ∈ E, (mult χ ρ : ℂ) / (s - ρ)‖ ≤
      Cw * Real.log (N * (|t + 2| + 2)) + Cw * Real.log (N * (|t - 2| + 2)) := by sorry
