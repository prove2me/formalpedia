-- Prove2me | Theorems.Thm_PIW_AdelClassFin_stDict
-- name    : PIW.AdelClassFin.stDict
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:52:51.177128+00:00
-- url     : https://prove2.me/theorems/bd36b7fd-4150-5ad9-b94f-7937f843fbea
-- title:
--   Adel Class Fin: st Dict
-- statement:
--   The Adel Class Fin construction uses the st Dict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictAll.lean#L22-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictAll.lean#L22-L22

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdelClassFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_StGenusOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictInter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PIW PIW.AdelClassFin

theorem PIW.AdelClassFin.stDict : StDict := by sorry
