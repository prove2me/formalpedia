-- Prove2me | Theorems.Thm_PI_WeylForKWork_prod_split
-- name    : PI.WeylForKWork.prod_split
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:48:15.492489+00:00
-- url     : https://prove2.me/theorems/48080e4b-de57-4b3a-8072-ca87a683aa50
-- title:
--   Weyl For KWork: prod split
-- statement:
--   The Weyl For KWork construction uses the prod split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Formula.lean#L42-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Formula.lean#L42-L45

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Formula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WeylForKWork
open PI PI.UpqRep Matrix Finset
variable {N : ℕ}

theorem PI.WeylForKWork.prod_split {M : Type*} [CommMonoid M] (ε : Fin N → Bool) (f : Fin N → M) :
    ∏ a, f a = (∏ i, f (ePl ε i)) * ∏ j, f (eMi ε j) := by sorry
