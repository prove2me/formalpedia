-- Prove2me | Theorems.Thm_PIW_AdelClassFin_DictGen_fmat_inv_mul
-- name    : PIW.AdelClassFin.DictGen.fmat_inv_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:28:16.837352+00:00
-- url     : https://prove2.me/theorems/3a383eb9-d561-4d68-86bd-3af5bcd2a323
-- title:
--   Dict Gen: fmat inv mul
-- statement:
--   The Dict Gen construction uses the fmat inv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictGen.lean#L52-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictGen.lean#L52-L55

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
open PIW.AdelClassFin.DictGen
variable (I : AutInst)

theorem PIW.AdelClassFin.DictGen.fmat_inv_mul (x : I.Gf) : I.fmat x⁻¹ * I.fmat x = 1 := by sorry
