-- Prove2me | Theorems.Thm_PIW_AdelClassFin_adelClassFin_of_svReal
-- name    : PIW.AdelClassFin.adelClassFin_of_svReal
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:49:06.106065+00:00
-- url     : https://prove2.me/theorems/811c4594-4105-48d5-9ba2-fe33a736a11e
-- title:
--   Adel Class Fin: adel Class Fin of sv Real
-- statement:
--   The Adel Class Fin construction uses the adel Class Fin of sv Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/AdelClassFinOfSvReal.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/AdelClassFinOfSvReal.lean#L13-L14

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_Partial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_ExistsBoundedMultiplier
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SuccessiveVectorCodifferent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SuccessiveVectorBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SuccessiveVectorGramDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SuccessiveVectorMajorantE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_BlkMulVecCat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_AdelClassFinOfSvReal
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

theorem PIW.AdelClassFin.adelClassFin_of_svReal (h : SvReal) : PI.AdelClassFin.AdelClassFin := by sorry
