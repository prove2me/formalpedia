-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_classFinite_of
-- name    : PI.UnitaryGroupMassFormula.UJClassFin.classFinite_of
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:40:03.353802+00:00
-- url     : https://prove2.me/theorems/51e90178-e755-4575-9259-a6f1b8938c25
-- title:
--   UJClass Fin: class Finite of
-- statement:
--   The UJClass Fin construction uses the class Finite of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/ClassFiniteOf.lean#L65-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/ClassFiniteOf.lean#L65-L77

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_HermLatFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_ClassFiniteOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct ComplexOrder
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.UJClassFin
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem PI.UnitaryGroupMassFormula.UJClassFin.classFinite_of (hS : SigPos) (hA : AdelBounds) (hB : LatFin) : ClassFinite := by sorry
