-- Prove2me | Theorems.Thm_PI_FJMA_eq_C_of_support
-- name    : PI.FJMA.eq_C_of_support
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:40.872003+00:00
-- url     : https://prove2.me/theorems/44929aeb-b04e-442e-b8d6-ff47411ee2d8
-- title:
--   FJMA: eq C of support
-- statement:
--   The FJMA construction uses the eq C of support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/VarsZeroOfSupported.lean#L132-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/VarsZeroOfSupported.lean#L132-L140

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
variable {σ : Type}

theorem PI.FJMA.eq_C_of_support {Q : MvPolynomial σ ℂ} (h : ∀ e ∈ Q.support, e = 0) : Q = C (coeff 0 Q) := by sorry
