-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_arith_real
-- name    : PI.UnitaryGroupMassFormula.LocJacTyp.arith_real
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:32:57.153325+00:00
-- url     : https://prove2.me/theorems/5ce095ae-b9e5-555c-a006-794068548f57
-- title:
--   Loc Jac Typ: arith real
-- statement:
--   The Loc Jac Typ construction uses the arith real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ExpProductSquareInv.lean#L153-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ExpProductSquareInv.lean#L153-L204

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

theorem PI.UnitaryGroupMassFormula.LocJacTyp.arith_real (r : ℕ) (A : Fin (r + 1) → ℝ) (hA : ∀ i, 0 < A i) (G m : ℝ) (hG : 0 < G) :
    m ^ ((r + 1) * (r + 1)) * G ^ (3 * ((r + 1) * (r + 1))) *
        (∏ i : Fin (r + 1), ∏ j : Fin (r + 1), ((A i * A j) ^ 2)⁻¹) *
        ∏ l : Fin r, (((∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => (i : ℕ) ≤ (l : ℕ)),
          A i ^ 2) * G⁻¹ ^ ((l : ℕ) + 1)) ^ 2) ^ 2 =
      (∏ q : UIdx r, (m ^ 2 * G ^ 2 * (A q.1.1 / A q.1.2) ^ 4)) *
        ∏ l : Fin (r + 1), (m * G ^ 3 * (A l ^ 4)⁻¹) := by sorry
