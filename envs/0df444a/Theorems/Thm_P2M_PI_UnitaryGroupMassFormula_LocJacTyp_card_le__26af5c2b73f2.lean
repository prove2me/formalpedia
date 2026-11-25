-- Prove2me | Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_LocJacTyp_card_le__26af5c2b73f2
-- name    : P2M_PI_UnitaryGroupMassFormula_LocJacTyp_card_le__26af5c2b73f2
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:00:20.299637+00:00
-- url     : https://prove2.me/theorems/a4f7b71f-4ae3-563e-bfbf-31246f2dd9eb
-- title:
--   P2 M PI Unitary Group Mass Formula Loc Jac Typ card le  26af5c2b73f2: P2 M PI Unitary Group Mass Formula Loc Jac Typ card le  26af5c2b73f2
-- statement:
--   The P2 M PI Unitary Group Mass Formula Loc Jac Typ card le  26af5c2b73f2 construction uses the P2 M PI Unitary Group Mass Formula Loc Jac Typ card le  26af5c2b73f2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ExpProductSquareInv.lean#L32-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ExpProductSquareInv.lean#L32-L42

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

theorem P2M_PI_UnitaryGroupMassFormula_LocJacTyp_card_le__26af5c2b73f2 (r : ℕ) (i : Fin (r + 1)) :
    ((Finset.univ.filter fun l : Fin r => (i : ℕ) ≤ (l : ℕ)).card : ℝ) = (r : ℝ) - (i : ℕ) := by sorry

alias «PI».«UnitaryGroupMassFormula».«LocJacTyp».«card_le'» := P2M_PI_UnitaryGroupMassFormula_LocJacTyp_card_le__26af5c2b73f2
