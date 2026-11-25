-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_herm_add_left
-- name    : PI.UnitaryGroupMassFormula.UJClassFin.herm_add_left
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:40:36.427955+00:00
-- url     : https://prove2.me/theorems/c47de0d5-d774-4a5b-a97f-94dbb92f002e
-- title:
--   UJClass Fin: herm add left
-- statement:
--   The UJClass Fin construction uses the herm add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/HermSingleLeft.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/HermSingleLeft.lean#L14-L15

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

theorem PI.UnitaryGroupMassFormula.UJClassFin.herm_add_left (x x' y : Fin M → E) : herm σ J (x + x') y = herm σ J x y + herm σ J x' y := by sorry
