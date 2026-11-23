-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_sum_uidx
-- name    : PI.UnitaryGroupMassFormula.LocJacTyp.sum_uidx
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:59:02.753696+00:00
-- url     : https://prove2.me/theorems/f135b51f-8792-4a46-aaaf-bb36d97c00a9
-- title:
--   Loc Jac Typ: sum uidx
-- statement:
--   The Loc Jac Typ construction uses the sum uidx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ExpProductSquareInv.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ExpProductSquareInv.lean#L15-L18

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

theorem PI.UnitaryGroupMassFormula.LocJacTyp.sum_uidx (r : ℕ) (g : Fin (r + 1) × Fin (r + 1) → ℝ) :
    ∑ q : UIdx r, g q.1 = ∑ i : Fin (r + 1), ∑ j : Fin (r + 1), if i < j then g (i, j) else 0 := by sorry
