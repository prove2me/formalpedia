-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_eJ
-- name    : PI.UnitaryGroupMassFormula.LocJacTyp.eJ
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:32:16.188146+00:00
-- url     : https://prove2.me/theorems/a30a7762-fbcc-4ce7-bd5d-4ee5ebc62b89
-- title:
--   Loc Jac Typ: e J
-- statement:
--   The Loc Jac Typ construction uses the e J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ExpProductSquareInv.lean#L100-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ExpProductSquareInv.lean#L100-L114

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

theorem PI.UnitaryGroupMassFormula.LocJacTyp.eJ (a : Fin (r + 1) → ℝ) (γ : ℝ) :
    ∏ l : Fin r, (((∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => (i : ℕ) ≤ (l : ℕ)),
        exp (a i) ^ 2) * (exp γ)⁻¹ ^ ((l : ℕ) + 1)) ^ 2) ^ 2 =
      exp (8 * ∑ i : Fin (r + 1), ((r : ℝ) - (i : ℕ)) * a i -
        4 * γ * ∑ l : Fin r, (((l : ℕ) : ℝ) + 1)) := by sorry
