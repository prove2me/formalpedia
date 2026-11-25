-- Prove2me | Theorems.Thm_PI_DefPosDefWork_re_nonneg_of_rat
-- name    : PI.DefPosDefWork.re_nonneg_of_rat
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:27:04.120095+00:00
-- url     : https://prove2.me/theorems/f550c450-6138-5bee-85a0-2038a4b7327d
-- title:
--   Def Pos Def Work: re nonneg of rat
-- statement:
--   The Def Pos Def Work construction uses the re nonneg of rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PositiveDefiniteness/PositiveDefiniteSecond.lean#L10-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PositiveDefiniteness/PositiveDefiniteSecond.lean#L10-L32

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PositiveDefiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PositiveDefiniteness_PositiveDefiniteSecond
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DefPosDefWork
open Matrix ComplexOrder

theorem PI.DefPosDefWork.re_nonneg_of_rat {k : ℕ} (M : Matrix (Fin k) (Fin k) ℂ) (z : ℂ) (hz : z.im ≠ 0)
    (h : ∀ α β : Fin k → ℚ, 0 ≤ (star (fun i => (α i : ℂ) + (β i : ℂ) * z) ⬝ᵥ
      (M *ᵥ (fun i => (α i : ℂ) + (β i : ℂ) * z))).re)
    (v : Fin k → ℂ) : 0 ≤ (star v ⬝ᵥ (M *ᵥ v)).re := by sorry
