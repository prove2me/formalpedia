-- Prove2me | Theorems.Thm_PIW_AdelClassFin_iv_add_smul
-- name    : PIW.AdelClassFin.iv_add_smul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:47:37.847805+00:00
-- url     : https://prove2.me/theorems/390669ca-aaac-416f-8723-4785b2c5c692
-- title:
--   Adel Class Fin: iv add smul
-- statement:
--   The Adel Class Fin construction uses the iv add smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/KsetMulVecMem.lean#L113-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/KsetMulVecMem.lean#L113-L116

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_StGenusOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_KsetMulVecMem
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

theorem PIW.AdelClassFin.iv_add_smul (I : AutInst) (r l : Fin I.n → I.E) (g : ℕ) :
    iv I (r + (g : ℤ) • l) = iv I r + (g : I.E ⊗[I.F] Af I.F) • iv I l := by sorry
