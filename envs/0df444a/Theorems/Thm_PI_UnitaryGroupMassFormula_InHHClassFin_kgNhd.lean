-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_kgNhd
-- name    : PI.UnitaryGroupMassFormula.InHHClassFin.kgNhd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:43:39.397801+00:00
-- url     : https://prove2.me/theorems/78a398aa-9dd8-4911-bb81-9596d9199102
-- title:
--   In HHClass Fin: kg Nhd
-- statement:
--   The In HHClass Fin construction uses the kg Nhd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/OneMemKg.lean#L16-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/OneMemKg.lean#L16-L26

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_OneMemKg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix IsDedekindDomain Formalism.UG PI.InHHClassFin
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin

theorem PI.UnitaryGroupMassFormula.InHHClassFin.kgNhd : KgNhd := by sorry
