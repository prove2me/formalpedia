-- Prove2me | Theorems.Thm_PI_FJMX_shapeProd_hom_row
-- name    : PI.FJMX.shapeProd_hom_row
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:31:04.388628+00:00
-- url     : https://prove2.me/theorems/7ee03f7e-105d-4b2d-b56c-f52a3657bb37
-- title:
--   FJMX: shape Prod hom row
-- statement:
--   The FJMX construction uses the shape Prod hom row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistWt.lean#L151-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistWt.lean#L151-L155

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistWt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial FockH1Action PI.FJM
noncomputable section
open PI PI.FJMX
variable {p q r s m k : ℕ}

theorem PI.FJMX.shapeProd_hom_row (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s) (w : Ln p q r s → ℕ) (i₀ : Fin m)
    (hw : ∀ i j, w (ρ i, κ j) = if i = i₀ then 1 else 0) (α : List ℕ) (hα : α.Pairwise (· ≥ ·)) :
    IsWeightedHomogeneous w (shapeProd (varMat ρ κ) α) (α.getD i₀.val 0) := by sorry
