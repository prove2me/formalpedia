-- Prove2me | Theorems.Thm_PI_FJMB_bCol_mul_free
-- name    : PI.FJMB.bCol_mul_free
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:30.605282+00:00
-- url     : https://prove2.me/theorems/64b5a847-44c2-4ac1-8bea-d0c9995d31cb
-- title:
--   FJMB: b Col mul free
-- statement:
--   The FJMB construction uses the b Col mul free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurCauchy.lean#L77-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurCauchy.lean#L77-L87

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurDiag
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurCauchy
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Classical
open PI PI.FJMB
variable {σ : Type*}

theorem PI.FJMB.bCol_mul_free {m n : ℕ} (ι : Fin m × Fin n → σ) (c d : Fin n) (S Q : MvPolynomial σ ℂ)
    (hQ : ∀ e ∈ Q.support, ∀ x, e (ι x) = 0) : PI.FJM.bCol ι c d (S * Q) = PI.FJM.bCol ι c d S * Q := by sorry
