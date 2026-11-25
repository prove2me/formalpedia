-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_eU
-- name    : PI.UnitaryGroupMassFormula.LocJacTyp.eU
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:32:35.01724+00:00
-- url     : https://prove2.me/theorems/a168005e-3444-5d24-ac39-7f5b69d0fb45
-- title:
--   Loc Jac Typ: e U
-- statement:
--   The Loc Jac Typ construction uses the e U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ExpProductSquareInv.lean#L116-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ExpProductSquareInv.lean#L116-L126

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

theorem PI.UnitaryGroupMassFormula.LocJacTyp.eU (a : Fin (r + 1) → ℝ) (γ : ℝ) :
    ∏ q : UIdx r, (exp γ ^ 2 * (exp (a q.1.1) / exp (a q.1.2)) ^ 4) =
      exp (2 * γ * (Fintype.card (UIdx r) : ℝ) + 4 * ∑ i : Fin (r + 1), ((r : ℝ) - (i : ℕ)) * a i -
        4 * ∑ j : Fin (r + 1), ((j : ℕ) : ℝ) * a j) := by sorry
