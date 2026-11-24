-- Prove2me | Theorems.Thm_PI_FJMX_shapeProd_hom_of
-- name    : PI.FJMX.shapeProd_hom_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:56.85571+00:00
-- url     : https://prove2.me/theorems/7ea53c38-40f6-47ce-b16e-67a20337a3e4
-- title:
--   FJMX: shape Prod hom of
-- statement:
--   The FJMX construction uses the shape Prod hom of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistWt.lean#L144-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistWt.lean#L144-L149

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

theorem PI.FJMX.shapeProd_hom_of (M : Matrix (Fin m) (Fin k) (Pol p q r s)) (w : Ln p q r s → ℕ) (α : List ℕ)
    (deg : ℕ → ℕ) (h : ∀ t, IsWeightedHomogeneous w (leadT M t) (deg t)) :
    IsWeightedHomogeneous w (shapeProd M α)
      (∑ t ∈ Finset.range α.length, (α.getD t 0 - α.getD (t + 1) 0) • deg (t + 1)) := by sorry
