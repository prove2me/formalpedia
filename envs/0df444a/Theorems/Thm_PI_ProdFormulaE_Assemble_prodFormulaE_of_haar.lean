-- Prove2me | Theorems.Thm_PI_ProdFormulaE_Assemble_prodFormulaE_of_haar
-- name    : PI.ProdFormulaE.Assemble.prodFormulaE_of_haar
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:00:11.286949+00:00
-- url     : https://prove2.me/theorems/bdab9367-4907-4533-906d-1c280b2c4491
-- title:
--   Assemble: prod Formula E of haar
-- statement:
--   The Assemble construction uses the prod Formula E of haar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/Assemble.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/Assemble.lean#L11-L12

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ProdFormulaE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ProdFormulaEOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_SumLocalTrace
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormTraceLeOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ResChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_Assemble
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.ProdFormulaE PI.ProdFormulaE.Assemble

theorem PI.ProdFormulaE.Assemble.prodFormulaE_of_haar (hH : St.HaarAlg) : PI.ProdFormulaE.ProdFormulaE := by sorry
