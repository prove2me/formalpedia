-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_sum_fst
-- name    : PI.UnitaryGroupMassFormula.LocJacTyp.sum_fst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:58:16.709119+00:00
-- url     : https://prove2.me/theorems/571562f4-14f2-4d79-ae9b-3773f79b15ab
-- title:
--   Loc Jac Typ: sum fst
-- statement:
--   The Loc Jac Typ construction uses the sum fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ExpProductSquareInv.lean#L44-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ExpProductSquareInv.lean#L44-L50

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

theorem PI.UnitaryGroupMassFormula.LocJacTyp.sum_fst (r : ℕ) (f : Fin (r + 1) → ℝ) :
    ∑ q : UIdx r, f q.1.1 = ∑ i : Fin (r + 1), ((r : ℝ) - (i : ℕ)) * f i := by sorry
