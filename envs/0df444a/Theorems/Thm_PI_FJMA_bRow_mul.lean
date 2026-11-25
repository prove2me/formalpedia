-- Prove2me | Theorems.Thm_PI_FJMA_bRow_mul
-- name    : PI.FJMA.bRow_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:15.499226+00:00
-- url     : https://prove2.me/theorems/b9f93685-86b1-4aa2-a158-1d3676bbcf2d
-- title:
--   FJMA: b Row mul
-- statement:
--   The FJMA construction uses the b Row mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/VarsZeroOfSupported.lean#L66-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/VarsZeroOfSupported.lean#L66-L71

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

theorem PI.FJMA.bRow_mul {m n : ℕ} (ι : Fin m × Fin n → σ) (a b : Fin m) (F G : MvPolynomial σ ℂ)
    (hF : ∀ x, pderiv (ι x) F = 0) : bRow ι a b (F * G) = F * bRow ι a b G := by sorry
