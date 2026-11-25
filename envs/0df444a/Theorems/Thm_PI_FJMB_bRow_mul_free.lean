-- Prove2me | Theorems.Thm_PI_FJMB_bRow_mul_free
-- name    : PI.FJMB.bRow_mul_free
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:32.448511+00:00
-- url     : https://prove2.me/theorems/d6f3a0fe-866b-5b46-adf0-c7c55c8dcd5b
-- title:
--   FJMB: b Row mul free
-- statement:
--   The FJMB construction uses the b Row mul free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurCauchy.lean#L65-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurCauchy.lean#L65-L75

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

theorem PI.FJMB.bRow_mul_free {m n : ℕ} (ι : Fin m × Fin n → σ) (a b : Fin m) (S Q : MvPolynomial σ ℂ)
    (hQ : ∀ e ∈ Q.support, ∀ x, e (ι x) = 0) : PI.FJM.bRow ι a b (S * Q) = PI.FJM.bRow ι a b S * Q := by sorry
