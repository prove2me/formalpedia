-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_herm_smul_right
-- name    : PI.UnitaryGroupMassFormula.UJClassFin.herm_smul_right
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:01:57.663611+00:00
-- url     : https://prove2.me/theorems/a1162ade-e04a-568c-b095-2ecf681ac93f
-- title:
--   UJClass Fin: herm smul right
-- statement:
--   The UJClass Fin construction uses the herm smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/HermSingleLeft.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/HermSingleLeft.lean#L25-L28

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

theorem PI.UnitaryGroupMassFormula.UJClassFin.herm_smul_right (a : E) (x y : Fin M → E) : herm σ J x (a • y) = a * herm σ J x y := by sorry
