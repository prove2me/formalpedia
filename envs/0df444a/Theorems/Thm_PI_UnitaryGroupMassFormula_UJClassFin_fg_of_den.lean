-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_fg_of_den
-- name    : PI.UnitaryGroupMassFormula.UJClassFin.fg_of_den
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:56:47.707055+00:00
-- url     : https://prove2.me/theorems/2d075292-2530-4ee6-83c1-8e5337b9dcf9
-- title:
--   UJClass Fin: fg of den
-- statement:
--   The UJClass Fin construction uses the fg of den property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/HermSingleLeft.lean#L53-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/HermSingleLeft.lean#L53-L79

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_ClassFiniteOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_HermSingleLeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField
open scoped ComplexOrder
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.HermLatFin
variable {E : Type} [Field E] {M : ℕ} (σ : E →+* E) (J : Matrix (Fin M) (Fin M) E)
variable [NumberField E]

theorem PI.UnitaryGroupMassFormula.UJClassFin.fg_of_den (N : Submodule (𝓞 E) (Fin M → E)) (d : ℕ) (hd : 0 < d)
    (h : ∀ y ∈ N, ∀ j, IsIntegral ℤ ((d : E) * y j)) : N.FG := by sorry
