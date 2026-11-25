-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ScalDeg_prod_fiber
-- name    : PI.UnitaryGroupMassFormula.ScalDeg.prod_fiber
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:40:14.269951+00:00
-- url     : https://prove2.me/theorems/c02435d2-5c69-58ca-afe4-143f95206bdc
-- title:
--   Scal Deg: prod fiber
-- statement:
--   The Scal Deg construction uses the prod fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarDegree/ScalDegMain.lean#L12-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarDegree/ScalDegMain.lean#L12-L21

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScalDeg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarDegree_ScalDegMain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScalDeg
open MvPolynomial PI.ScalDeg
open Classical

theorem PI.UnitaryGroupMassFormula.ScalDeg.prod_fiber {T : Type} [Fintype T] {N : ℕ} (s : T → ℂ) (v : FrV T N →₀ ℕ) :
    (v.prod fun k n => s k.1 ^ n) =
      ∏ τ, s τ ^ (v.sum fun k n => if k.1 = τ then n else 0) := by sorry
