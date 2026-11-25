-- Prove2me | Theorems.Thm_PI_FJMB_cd_mono_factor
-- name    : PI.FJMB.cd_mono_factor
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:30:43.072677+00:00
-- url     : https://prove2.me/theorems/0eb6205d-0a4a-5d63-b6b1-06a6c731cec3
-- title:
--   FJMB: cd mono factor
-- statement:
--   The FJMB construction uses the cd mono factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/DiagonalImageBlockFree.lean#L11-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/DiagonalImageBlockFree.lean#L11-L74

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurCauchy
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_DiagonalImageBlockFree
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

theorem PI.FJMB.cd_mono_factor {m : ℕ} (ι : Fin m × Fin m → σ) (hι : Function.Injective ι) (e : σ →₀ ℕ) :
    aeval (killS (offD ι)) (monomial e (1 : ℂ)) =
      (∏ i, X (ι (i, i)) ^ (∑ k : Fin m, e (ι (i, k)))) * aeval (diagOne' ι) (monomial e (1 : ℂ)) := by sorry
