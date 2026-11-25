-- Prove2me | Theorems.Thm_PI_FJMA_dCAB
-- name    : PI.FJMA.dCAB
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:06.27487+00:00
-- url     : https://prove2.me/theorems/a5c9ca20-fa06-42cb-bb90-02497ede6299
-- title:
--   FJMA: d CAB
-- statement:
--   The FJMA construction uses the d CAB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/VarsZeroOfSupported.lean#L172-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/VarsZeroOfSupported.lean#L172-L173

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeProdVarMatNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_VarsZeroOfSupported
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMA
open PI.FJM
variable (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ)

theorem PI.FJMA.dCAB : ∀ x, ιC p q r s μ μ' x ∉ Set.range (ιA p q r s μ μ') ∪ Set.range (ιB p q r s μ μ') := by sorry
