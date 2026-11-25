-- Prove2me | Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_LocJacTyp_card_Ioi__ab9c340c690c
-- name    : P2M_PI_UnitaryGroupMassFormula_LocJacTyp_card_Ioi__ab9c340c690c
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:55:53.299398+00:00
-- url     : https://prove2.me/theorems/97d9eec7-c7dd-4426-89c2-bd9a559967a8
-- title:
--   P2 M PI Unitary Group Mass Formula Loc Jac Typ card Ioi  ab9c340c690c: P2 M PI Unitary Group Mass Formula Loc Jac Typ card Ioi  ab9c340c690c
-- statement:
--   The P2 M PI Unitary Group Mass Formula Loc Jac Typ card Ioi  ab9c340c690c construction uses the P2 M PI Unitary Group Mass Formula Loc Jac Typ card Ioi  ab9c340c690c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ExpProductSquareInv.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ExpProductSquareInv.lean#L20-L25

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

theorem P2M_PI_UnitaryGroupMassFormula_LocJacTyp_card_Ioi__ab9c340c690c (r : ℕ) (i : Fin (r + 1)) :
    ((Finset.univ.filter fun j : Fin (r + 1) => i < j).card : ℝ) = (r : ℝ) - (i : ℕ) := by sorry

alias «PI».«UnitaryGroupMassFormula».«LocJacTyp».«card_Ioi'» := P2M_PI_UnitaryGroupMassFormula_LocJacTyp_card_Ioi__ab9c340c690c
