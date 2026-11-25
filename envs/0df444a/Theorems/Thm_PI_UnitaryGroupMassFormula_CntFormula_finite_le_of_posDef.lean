-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_finite_le_of_posDef
-- name    : PI.UnitaryGroupMassFormula.CntFormula.finite_le_of_posDef
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:38:18.069428+00:00
-- url     : https://prove2.me/theorems/ecc725da-65fa-423e-aff3-e7f22dddf2c2
-- title:
--   Cnt Formula: finite le of pos Def
-- statement:
--   The Cnt Formula construction uses the finite le of pos Def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/FiniteLeOfPosDef.lean#L5-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/FiniteLeOfPosDef.lean#L5-L111

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_FiniteLeOfPosDef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula

theorem PI.UnitaryGroupMassFormula.CntFormula.finite_le_of_posDef {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (B : LinearMap.BilinForm ℚ V) (hS : ∀ x y, B x y = B y x) (hpos : ∀ v, v ≠ 0 → 0 < B v v)
    (A : Submodule ℤ V) (hA : A.FG) (c : ℚ) : {v | v ∈ A ∧ B v v ≤ c}.Finite := by sorry
