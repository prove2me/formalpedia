-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_exp_product_square_inv
-- name    : PI.UnitaryGroupMassFormula.LocJacTyp.exp_product_square_inv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:32:25.202869+00:00
-- url     : https://prove2.me/theorems/2fef9cee-9e61-411a-a94f-aaefbdb89d7a
-- title:
--   Loc Jac Typ: exp product square inv
-- statement:
--   The Loc Jac Typ construction uses the exp product square inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ExpProductSquareInv.lean#L90-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ExpProductSquareInv.lean#L90-L98

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

theorem PI.UnitaryGroupMassFormula.LocJacTyp.exp_product_square_inv (a : Fin (r + 1) → ℝ) :
    ∏ i : Fin (r + 1), ∏ j : Fin (r + 1), ((exp (a i) * exp (a j)) ^ 2)⁻¹ =
      exp (-(4 * ((r : ℝ) + 1)) * ∑ i, a i) := by sorry
