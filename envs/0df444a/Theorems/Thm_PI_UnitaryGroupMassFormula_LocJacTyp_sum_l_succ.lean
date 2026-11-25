-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_sum_l_succ
-- name    : PI.UnitaryGroupMassFormula.LocJacTyp.sum_l_succ
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:32:38.502794+00:00
-- url     : https://prove2.me/theorems/78505d00-2686-4331-9361-68d47b2c1848
-- title:
--   Loc Jac Typ: sum l succ
-- statement:
--   The Loc Jac Typ construction uses the sum l succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ExpProductSquareInv.lean#L76-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ExpProductSquareInv.lean#L76-L80

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

theorem PI.UnitaryGroupMassFormula.LocJacTyp.sum_l_succ (r : ℕ) : ∑ l : Fin r, (((l : ℕ) : ℝ) + 1) = ∑ i : Fin (r + 1), ((i : ℕ) : ℝ) := by sorry
