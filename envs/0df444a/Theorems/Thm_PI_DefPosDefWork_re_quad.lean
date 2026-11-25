-- Prove2me | Theorems.Thm_PI_DefPosDefWork_re_quad
-- name    : PI.DefPosDefWork.re_quad
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:27:08.13374+00:00
-- url     : https://prove2.me/theorems/947bfc74-a6c1-5bd2-a738-f0c280aedfc6
-- title:
--   Def Pos Def Work: re quad
-- statement:
--   The Def Pos Def Work construction uses the re quad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PositiveDefiniteness/PositiveDefiniteSecond.lean#L34-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PositiveDefiniteness/PositiveDefiniteSecond.lean#L34-L47

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

theorem PI.DefPosDefWork.re_quad {k : ℕ} (N : Matrix (Fin k) (Fin k) ℂ) (hN : ∀ i j, (N i j).im = 0) (a b : Fin k → ℝ) :
    (star (fun i => (a i : ℂ) + (b i : ℂ) * Complex.I) ⬝ᵥ (N *ᵥ (fun i => (a i : ℂ) + (b i : ℂ) * Complex.I))).re
      = (star (fun i => (a i : ℂ)) ⬝ᵥ (N *ᵥ (fun i => (a i : ℂ)))).re
        + (star (fun i => (b i : ℂ)) ⬝ᵥ (N *ᵥ (fun i => (b i : ℂ)))).re := by sorry
