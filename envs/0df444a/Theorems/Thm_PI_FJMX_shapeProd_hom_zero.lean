-- Prove2me | Theorems.Thm_PI_FJMX_shapeProd_hom_zero
-- name    : PI.FJMX.shapeProd_hom_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:33.9019+00:00
-- url     : https://prove2.me/theorems/fc04493f-b222-4b61-bf91-4f82c6b92770
-- title:
--   FJMX: shape Prod hom zero
-- statement:
--   The FJMX construction uses the shape Prod hom zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistWt.lean#L163-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistWt.lean#L163-L167

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

theorem PI.FJMX.shapeProd_hom_zero (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s) (w : Ln p q r s → ℕ)
    (hw : ∀ i j, w (ρ i, κ j) = 0) (α : List ℕ) :
    IsWeightedHomogeneous w (shapeProd (varMat ρ κ) α) 0 := by sorry
