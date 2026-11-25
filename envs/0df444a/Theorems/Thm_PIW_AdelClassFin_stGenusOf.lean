-- Prove2me | Theorems.Thm_PIW_AdelClassFin_stGenusOf
-- name    : PIW.AdelClassFin.stGenusOf
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:48:35.01577+00:00
-- url     : https://prove2.me/theorems/9da9da20-649c-41e3-9fc5-edd35a6c00cb
-- title:
--   Adel Class Fin: st Genus Of
-- statement:
--   The Adel Class Fin construction uses the st Genus Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/IsImgTrans.lean#L44-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/IsImgTrans.lean#L44-L80

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_StGenusOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_IsImgTrans
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

theorem PIW.AdelClassFin.stGenusOf : StGenusOf := by sorry
