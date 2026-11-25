-- Prove2me | Theorems.Thm_PI_FJMA_bCol_mul
-- name    : PI.FJMA.bCol_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:30:22.382+00:00
-- url     : https://prove2.me/theorems/9ec3325c-feca-53b8-a81a-289ef35421c8
-- title:
--   FJMA: b Col mul
-- statement:
--   The FJMA construction uses the b Col mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/VarsZeroOfSupported.lean#L73-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/VarsZeroOfSupported.lean#L73-L78

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

theorem PI.FJMA.bCol_mul {m n : ℕ} (ι : Fin m × Fin n → σ) (c d : Fin n) (F G : MvPolynomial σ ℂ)
    (hF : ∀ x, pderiv (ι x) F = 0) : bCol ι c d (F * G) = F * bCol ι c d G := by sorry
