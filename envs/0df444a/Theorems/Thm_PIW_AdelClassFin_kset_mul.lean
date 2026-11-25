-- Prove2me | Theorems.Thm_PIW_AdelClassFin_kset_mul
-- name    : PIW.AdelClassFin.kset_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:49:03.486721+00:00
-- url     : https://prove2.me/theorems/a53d0736-f25c-4bc0-9b13-d1a35178c359
-- title:
--   Adel Class Fin: kset mul
-- statement:
--   The Adel Class Fin construction uses the kset mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/KsetMulVecMem.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/KsetMulVecMem.lean#L24-L27

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

theorem PIW.AdelClassFin.kset_mul (I : AutInst) {k t : I.Gf} (hk : k ∈ I.Kset) (ht : t ∈ I.Kset) : k * t ∈ I.Kset := by sorry
