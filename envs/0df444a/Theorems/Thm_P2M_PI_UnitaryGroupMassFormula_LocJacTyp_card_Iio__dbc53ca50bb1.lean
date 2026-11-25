-- Prove2me | Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_LocJacTyp_card_Iio__dbc53ca50bb1
-- name    : P2M_PI_UnitaryGroupMassFormula_LocJacTyp_card_Iio__dbc53ca50bb1
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:00:58.860505+00:00
-- url     : https://prove2.me/theorems/770e01b8-fead-4b8a-9ee1-86caaafedef0
-- title:
--   P2 M PI Unitary Group Mass Formula Loc Jac Typ card Iio  dbc53ca50bb1: P2 M PI Unitary Group Mass Formula Loc Jac Typ card Iio  dbc53ca50bb1
-- statement:
--   The P2 M PI Unitary Group Mass Formula Loc Jac Typ card Iio  dbc53ca50bb1 construction uses the P2 M PI Unitary Group Mass Formula Loc Jac Typ card Iio  dbc53ca50bb1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ExpProductSquareInv.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ExpProductSquareInv.lean#L27-L30

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

theorem P2M_PI_UnitaryGroupMassFormula_LocJacTyp_card_Iio__dbc53ca50bb1 (r : ℕ) (j : Fin (r + 1)) :
    ((Finset.univ.filter fun i : Fin (r + 1) => i < j).card : ℝ) = ((j : ℕ) : ℝ) := by sorry

alias «PI».«UnitaryGroupMassFormula».«LocJacTyp».«card_Iio'» := P2M_PI_UnitaryGroupMassFormula_LocJacTyp_card_Iio__dbc53ca50bb1
