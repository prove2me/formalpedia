-- Prove2me | Theorems.Thm_PI_FJMB_col_inv
-- name    : PI.FJMB.col_inv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:30:48.821373+00:00
-- url     : https://prove2.me/theorems/4c5cee5e-f587-5535-91fe-9849ec46758d
-- title:
--   FJMB: col inv
-- statement:
--   The FJMB construction uses the col inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurInv.lean#L91-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurInv.lean#L91-L118

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurChain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FJMB
variable {σ : Type*}

theorem PI.FJMB.col_inv {m n : ℕ} (ι : Fin m × Fin n → σ) (hι : Function.Injective ι) (c d : Fin n) (hcd : c ≠ d)
    (f : MvPolynomial σ ℂ) (hf : PI.FJM.bCol ι c d f = 0) {K : Type*} [Field K] [CharZero K] [Algebra ℂ K]
    (M : Fin m → Fin n → K) (p : σ → K) (t : K) :
    aeval (fill ι (colAddM M c d t) p) f = aeval (fill ι M p) f := by sorry
