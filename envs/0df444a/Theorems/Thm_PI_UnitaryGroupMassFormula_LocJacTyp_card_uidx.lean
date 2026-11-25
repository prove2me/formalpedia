-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_card_uidx
-- name    : PI.UnitaryGroupMassFormula.LocJacTyp.card_uidx
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:32:12.319613+00:00
-- url     : https://prove2.me/theorems/d4f5f286-77ae-5d40-bed7-0af79a9e3e05
-- title:
--   Loc Jac Typ: card uidx
-- statement:
--   The Loc Jac Typ construction uses the card uidx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ExpProductSquareInv.lean#L138-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ExpProductSquareInv.lean#L138-L145

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

theorem PI.UnitaryGroupMassFormula.LocJacTyp.card_uidx : 2 * (Fintype.card (UIdx r) : ℝ) = (r : ℝ) * (r + 1) := by sorry
