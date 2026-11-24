-- Prove2me | Theorems.Thm_PIW_AdelClassFin_dictTop_fmat_mul
-- name    : PIW.AdelClassFin.dictTop_fmat_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:29:44.252417+00:00
-- url     : https://prove2.me/theorems/87bb14d2-2231-4914-ae5d-51e64583909e
-- title:
--   Adel Class Fin: dict Top fmat mul
-- statement:
--   The Adel Class Fin construction uses the dict Top fmat mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictTop.lean#L21-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictTop.lean#L21-L21

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictTop
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

theorem PIW.AdelClassFin.dictTop_fmat_mul (I : AutInst) (x y : I.Gf) : I.fmat (x * y) = I.fmat x * I.fmat y := by sorry
