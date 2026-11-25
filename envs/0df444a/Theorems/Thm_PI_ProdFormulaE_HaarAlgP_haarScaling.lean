-- Prove2me | Theorems.Thm_PI_ProdFormulaE_HaarAlgP_haarScaling
-- name    : PI.ProdFormulaE.HaarAlgP.haarScaling
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:01:26.510038+00:00
-- url     : https://prove2.me/theorems/bba554e1-aec6-481f-a071-59319d63d284
-- title:
--   Haar Alg P: haar Scaling
-- statement:
--   The Haar Alg P construction uses the haar Scaling property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/HaarAlg.lean#L7-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/HaarAlg.lean#L7-L12

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarScale
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarTransv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.ProdFormulaE PI.ProdFormulaE.HaarAlgP

theorem PI.ProdFormulaE.HaarAlgP.haarScaling : St.HaarAlg := by sorry
