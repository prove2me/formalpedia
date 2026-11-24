-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_int_sigma
-- name    : PI.UnitaryGroupMassFormula.UJClassFin.int_sigma
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:09:43.793743+00:00
-- url     : https://prove2.me/theorems/3a80ffdb-dfad-4077-9ca8-0bc01fc19914
-- title:
--   UJClass Fin: int sigma
-- statement:
--   The UJClass Fin construction uses the int sigma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/LatticeClassesFiniteRefinement.lean#L20-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/LatticeClassesFiniteRefinement.lean#L20-L20

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_HermSingleLeft
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_IsIntegralOfIntOE
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_HermLatFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_LatticeClassesFiniteRefinement
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
variable {E : Type} [Field E] [NumberField E]

theorem PI.UnitaryGroupMassFormula.UJClassFin.int_sigma (σ : E →+* E) {a : E} (ha : IsIntegral ℤ a) : IsIntegral ℤ (σ a) := by sorry
