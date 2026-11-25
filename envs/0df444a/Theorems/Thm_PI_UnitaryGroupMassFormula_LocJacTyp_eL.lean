-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_eL
-- name    : PI.UnitaryGroupMassFormula.LocJacTyp.eL
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:32:29.3508+00:00
-- url     : https://prove2.me/theorems/6d8508bb-4815-5278-b9f5-6aa091f26dc1
-- title:
--   Loc Jac Typ: e L
-- statement:
--   The Loc Jac Typ construction uses the e L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ExpProductSquareInv.lean#L128-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ExpProductSquareInv.lean#L128-L136

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ExpProductSquareInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacTyp
open scoped Classical
open Real
variable (r : ℕ)

theorem PI.UnitaryGroupMassFormula.LocJacTyp.eL (a : Fin (r + 1) → ℝ) (γ : ℝ) :
    ∏ l : Fin (r + 1), (exp γ ^ 3 * (exp (a l) ^ 4)⁻¹) =
      exp (3 * ((r : ℝ) + 1) * γ - 4 * ∑ l, a l) := by sorry
