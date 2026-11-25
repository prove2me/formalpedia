-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_uJClassFin_of
-- name    : PI.UnitaryGroupMassFormula.UJClassFin.uJClassFin_of
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:40:56.029613+00:00
-- url     : https://prove2.me/theorems/49e5442a-ffb4-5013-a3d8-d5a1c064745f
-- title:
--   UJClass Fin: u JClass Fin of
-- statement:
--   The UJClass Fin construction uses the u JClass Fin of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/UJClassFinOf.lean#L12-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/UJClassFinOf.lean#L12-L68

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_UJClassFinOf
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
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.UJClassFin

theorem PI.UnitaryGroupMassFormula.UJClassFin.uJClassFin_of (hR : RatDense) (hC : ClassFinite) : UJClassFin := by sorry
