-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_sum_jac
-- name    : PI.UnitaryGroupMassFormula.LocJacTyp.sum_jac
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:32:33.95847+00:00
-- url     : https://prove2.me/theorems/aed48a1d-b465-4ee1-958e-6444332d853c
-- title:
--   Loc Jac Typ: sum jac
-- statement:
--   The Loc Jac Typ construction uses the sum jac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ExpProductSquareInv.lean#L60-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ExpProductSquareInv.lean#L60-L66

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

theorem PI.UnitaryGroupMassFormula.LocJacTyp.sum_jac (r : ℕ) (a : Fin (r + 1) → ℝ) :
    ∑ l : Fin r, ∑ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => (i : ℕ) ≤ (l : ℕ)), a i =
      ∑ i : Fin (r + 1), ((r : ℝ) - (i : ℕ)) * a i := by sorry
