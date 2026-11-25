-- Prove2me | Theorems.Thm_PIW_AdelClassFin_gd_int_smul
-- name    : PIW.AdelClassFin.gd_int_smul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:48:18.692618+00:00
-- url     : https://prove2.me/theorems/de0b8138-49c1-46cc-8ddb-a15e289b9228
-- title:
--   Adel Class Fin: gd int smul
-- statement:
--   The Adel Class Fin construction uses the gd int smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/SuccessiveVectorGramDet.lean#L37-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/SuccessiveVectorGramDet.lean#L37-L38

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartShortOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSmulRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SuccessiveVectorGramDet
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
open Formalism.UG NumberField
open scoped Matrix
variable {E : Type} [Field E] [NumberField E] [StarRing E] {m : ℕ} (J : Matrix (Fin m) (Fin m) E)

theorem PIW.AdelClassFin.gd_int_smul (c : ℤ) (x : Fin m → E) : ((c : E)) • x = ((c : ℚ)) • x := by sorry
