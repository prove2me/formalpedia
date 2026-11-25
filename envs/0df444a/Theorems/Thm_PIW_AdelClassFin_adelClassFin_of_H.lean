-- Prove2me | Theorems.Thm_PIW_AdelClassFin_adelClassFin_of_H
-- name    : PIW.AdelClassFin.adelClassFin_of_H
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:49:41.23954+00:00
-- url     : https://prove2.me/theorems/b7de8544-9e48-4beb-8547-f1206dbefb79
-- title:
--   Adel Class Fin: adel Class Fin of H
-- statement:
--   The Adel Class Fin construction uses the adel Class Fin of H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/Partial.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/Partial.lean#L13-L14

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_IsImgTrans
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_KsetMulVecMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_StHOfOpen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_Partial
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

theorem PIW.AdelClassFin.adelClassFin_of_H (h : StH) : PI.AdelClassFin.AdelClassFin := by sorry
