-- Prove2me | Theorems.Thm_PI_HermLatFin_UnitaryGroupMassFormula_hform_apply
-- name    : PI.HermLatFin.UnitaryGroupMassFormula.hform_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:42:47.77414+00:00
-- url     : https://prove2.me/theorems/d06ec77e-1b6c-4504-839f-a2b0bd37b773
-- title:
--   Unitary Group Mass Formula: hform apply
-- statement:
--   The Unitary Group Mass Formula construction uses the hform apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianLatticeFiniteness/HformTracePos.lean#L59-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianLatticeFiniteness/HformTracePos.lean#L59-L60

import Definitions.Def_Formalism_PeriodIntegrals_HermLatFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianLatticeFiniteness_HformTracePos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped ComplexOrder
noncomputable section
open PI PI.HermLatFin PI.HermLatFin.UnitaryGroupMassFormula
variable {E : Type} [Field E] [NumberField E]
variable [StarRing E] {n : ℕ}

theorem PI.HermLatFin.UnitaryGroupMassFormula.hform_apply (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hform J x y = ∑ i, ∑ j, star (x i) * J i j * y j := by sorry
